#include "points_to_graph.h"
#include "var_recover.h"  // VarRecover::GetVarName 사용을 위해

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Constants.h"

#include <nlohmann/json.hpp>
#include <fstream>
#include <stack>
#include <sstream>

using json = nlohmann::json;
using namespace llvm;

// -------------------------
// PointsToGraph 구현
// -------------------------

bool PointsToGraph::addEdge(const Node &source, const Node &dest) {
  std::set<Node> &preds = ptr_graph[source];
  int prev = preds.size();
  preds.insert(dest);
  return prev != (int)preds.size();
}

void PointsToGraph::addBitCastEdge(const Node &source, const Node &dest) {
  // 현재는 ptr_graph에 별도 처리 없음 (확장 포인트)
}

void PointsToGraph::addNode(const Node &node) {
  ptr_graph[node]; // 키만 삽입하여 노드 등록
}

// -------------------------
// PointsToGraphOp 구현
// -------------------------

void PointsToGraphOp::exportToDot(PointsToGraph &ptg,
                                  const std::string &filename) {
  std::ofstream file(filename);
  if (!file.is_open()) {
    outs() << "Error: Unable to open file " << filename << "\n";
    return;
  }

  file << "digraph G {\n";
  for (const auto &pair : ptg.ptr_graph) {
    const Node &src = pair.first;
    const auto &dests = pair.second;

    if (dests.empty()) {
      file << "  \"" << src.getName() << "\";\n";
    } else {
      for (const Node &dest : dests) {
        file << "  \"" << src.getName() << "\" -> \""
             << dest.getName() << "\";\n";
      }
    }
  }
  file << "}\n";
  file.close();
  outs() << "Graph exported to " << filename << "\n";
}

void PointsToGraphOp::addNullNode(PointsToGraph &ptg) {
  Node null_node{"null", NodeType::Null};

  for (auto &pair : ptg.ptr_graph) {
    const Node &node = pair.first;
    const std::set<Node> &successors = pair.second;

    if (node.getType() == NodeType::Null || node.getType() == NodeType::Const)
      continue;

    if (successors.size() == 0) {
      ptg.addEdge(node, null_node);
    }
  }
}

void PointsToGraphOp::removeCycle(PointsToGraph &ptg) {
  while (removeCycleFunc(ptg)) {
  }
}

bool PointsToGraphOp::removeCycleFunc(PointsToGraph &ptg) {
  for (auto &pair : ptg.ptr_graph) {
    Node offset = pair.first;

    std::stack<Node> stack;
    std::map<Node, int> visited;
    std::map<Node, bool> in_stack;

    stack.push(offset);

    while (!stack.empty()) {
      Node current = stack.top();

      if (visited[current] == 0) {
        visited[current] = 1;
        in_stack[current] = true;

        bool pushed = false;
        for (const Node &next : ptg.ptr_graph[current]) {
          if (visited[next] == 0) {
            stack.push(next);
            pushed = true;
          } else if (in_stack[next]) {
            removeEdgeInCycle(ptg, current, next);
            return true;
          }
        }

        if (!pushed) {
          stack.pop();
          in_stack[current] = false;
          visited[current] = 2;
        }
      } else {
        stack.pop();
        in_stack[current] = false;
        visited[current] = 2;
      }
    }
  }
  return false;
}

void PointsToGraphOp::removeEdgeInCycle(PointsToGraph &ptg, const Node &source,
                                        const Node &dest) {
  Node new_source{source.getName() + "_c", NodeType::Local};
  std::set<Node> &preds = ptg.ptr_graph[source];

  preds.erase(dest);
  ptg.addBitCastEdge(source, new_source);
  ptg.addEdge(new_source, dest);
}

void PointsToGraphOp::addAnotherTypeNode(PointsToGraph &ptg,
                                         const std::string &offset) {
  std::ifstream file("/home/yujina/elis/pass/symex.json");
  json json_data;
  file >> json_data;
  file.close();

  const json *arr = nullptr;
  for (auto it = json_data.begin(); it != json_data.end(); ++it) {
    if (it.key().find(offset) != std::string::npos) {
      arr = &it.value();
      break;
    }
  }

  std::set<std::string> type_set;
  for (const auto &entry : *arr) {
    std::string ty = entry["type"].get<std::string>();
    if (ty.find("*") != std::string::npos)
      type_set.insert(ty);
  }

  if (type_set.size() != 1) {
    for (const std::string &type : type_set) {
      if (type == "i8*") {
        Node offset_node{offset, NodeType::Local};
        Node new_type_node{offset + "_i8", NodeType::Local};
        ptg.addBitCastEdge(offset_node, new_type_node);
      }
    }
  }
}

void PointsToGraphOp::initGraph(
    PointsToGraph &ptg,
    std::map<std::string, std::set<std::string>> offset_vars_map,
    std::map<int64_t, std::string> global_var_map) {   // 파라미터 추가
  for (auto &pair : offset_vars_map) {
    const std::string &offset = pair.first;
    if (offset == "argv.addr") continue;
    ptg.addNode(Node{offset, NodeType::Local});
  }

  // 전역변수 노드 등록 (엣지는 makePointsToGraph에서 채워짐)
  for (auto &pair : global_var_map) {
    ptg.addNode(Node{pair.second, NodeType::Global});
  }

  ptg.addNode(Node{"const", NodeType::Const});
}

// V가 (1) inttoptr(ConstantInt) 형태의 전역주소 상수식이거나
// (2) 전역주소 값을 그대로 담은 ConstantInt인 경우, global_var_map에서
// 매칭되는 이름을 찾아 Global 노드로 채워준다. 매칭 실패 시 false.
static bool TryResolveGlobalNode(
    Value *V,
    const std::map<int64_t, std::string> &global_var_map,
    Node &out) {
  int64_t addr = 0;

  if (auto *ce = dyn_cast<ConstantExpr>(V)) {
    if (ce->getOpcode() != Instruction::IntToPtr)
      return false;
    auto *ci = dyn_cast<ConstantInt>(ce->getOperand(0));
    if (!ci) return false;
    addr = ci->getSExtValue();
  } else if (auto *ci = dyn_cast<ConstantInt>(V)) {
    addr = ci->getSExtValue();
  } else {
    return false;
  }

  auto it = global_var_map.find(addr);
  if (it == global_var_map.end())
    return false;

  out = Node{it->second, NodeType::Global};
  return true;
}

void PointsToGraphOp::makePointsToGraph(
    PointsToGraph &ptg, Function &F,
    std::map<std::string, std::string> var_offset_map,
    std::map<int64_t, std::string> global_var_map) {   // 파라미터 추가
  VarRecover vr;

  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      if (StoreInst *store_inst = dyn_cast<StoreInst>(&I)) {
        Value *source = store_inst->getPointerOperand();
        Value *dest = store_inst->getValueOperand();

        std::string source_name = vr.GetVarName(F, source);
        std::string dest_name = vr.GetVarName(F, dest);

        // 전역변수 여부 판별
        Node global_source_node{"", NodeType::Global};
        Node global_dest_node{"", NodeType::Global};
        bool source_is_global = TryResolveGlobalNode(source, global_var_map, global_source_node);
        bool dest_is_global = TryResolveGlobalNode(dest, global_var_map, global_dest_node);

        bool source_is_offset = !source_is_global &&
            var_offset_map.find(source_name) != var_offset_map.end();
        bool dest_is_offset = !dest_is_global &&
            var_offset_map.find(dest_name) != var_offset_map.end();

        bool have_source = source_is_global || source_is_offset;
        Node source_node = source_is_global
            ? global_source_node
            : Node{var_offset_map[source_name], NodeType::Local};

        if (have_source) {
          if (dest_is_global) {
            // 전역 <- 전역/offset : gv_2 -> gv_1 케이스가 여기서 생성됨
            ptg.addEdge(source_node, global_dest_node);
          } else if (dest_is_offset) {
            Node dest_node{var_offset_map[dest_name], NodeType::Local};
            ptg.addEdge(source_node, dest_node);
          } else if (ConstantInt *ci = dyn_cast<ConstantInt>(dest)) {
            std::string const_node_name =
                ci->getType()->isIntegerTy(8) ? "const_i8" : "const_i32";
            Node const_node{const_node_name, NodeType::Const};
            ptg.addEdge(source_node, const_node);
          }
        }
      }

      if (LoadInst *load_inst = dyn_cast<LoadInst>(&I)) {
        Value *source = load_inst->getPointerOperand();

        std::string dest_name = vr.GetVarName(F, load_inst);
        std::string source_name = vr.GetVarName(F, source);

        Node global_source_node{"", NodeType::Global};
        bool source_is_global = TryResolveGlobalNode(source, global_var_map, global_source_node);
        bool source_is_offset = !source_is_global &&
            var_offset_map.find(source_name) != var_offset_map.end();
        bool dest_is_offset = var_offset_map.find(dest_name) != var_offset_map.end();

        if (dest_is_offset && (source_is_global || source_is_offset)) {
          Node dest_node{var_offset_map[dest_name], NodeType::Local};
          Node source_node = source_is_global
              ? global_source_node
              : Node{var_offset_map[source_name], NodeType::Local};
          ptg.addEdge(source_node, dest_node);
        }
      }
    }
  }
}

void PointsToGraphOp::addBitCastEdgeForMulTyNode(
    PointsToGraph &ptg,
    std::map<std::string, Type *> type_map,
    const std::string &source) {
  Node source_node{source, NodeType::Local};
  std::set<Node> &successors = ptg.ptr_graph[source_node];

  if (successors.size() == 0) {
    llvm::report_fatal_error("MAKE BITCAST EDGE: no successors!");
  }

  Type *base_type = type_map[successors.begin()->getName()];
  std::vector<Node> trash_can;
  int num = 1;

  for (const Node &succ : successors) {
    if (type_map[succ.getName()] != base_type) {
      trash_can.push_back(succ);

      Node new_source{source + "_" + std::to_string(num), NodeType::Local};
      ptg.addBitCastEdge(source_node, new_source);
      ptg.addEdge(new_source, succ);
      num++;
    }
  }

  for (const Node &t : trash_can) {
    successors.erase(t);
  }
}

// node.cc 내용 (stripPercent)도 여기에 포함
std::string stripPercent(const std::string &s) {
  if (!s.empty() && s[0] == '%')
    return s.substr(1);
  return s;
}
