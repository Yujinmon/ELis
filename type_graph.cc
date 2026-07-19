#include "type_graph.h"
#include "var_recover.h"  // VarRecover 전체 정의 필요

#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/Format.h"

#include <fstream>
#include <stack>
#include <climits>

using namespace llvm;

#include <sstream>
#include <cstdio>
#include <cctype>
#include <cstdint>

namespace {

struct RodataRange {
  bool valid = false;
  uint64_t start = 0;
  uint64_t offset = 0;
  uint64_t size = 0;
};

RodataRange getRodataRange(const std::string &binary) {
  RodataRange r;
  std::string cmd = "readelf -S " + binary + " | grep '\\.rodata'";
  FILE *pipe = popen(cmd.c_str(), "r");
  if (!pipe) return r;

  char buffer[256];
  std::string line;
  if (fgets(buffer, sizeof(buffer), pipe)) line = buffer;
  pclose(pipe);
  if (line.empty()) return r;

  for (char &c : line)
    if (c == '[' || c == ']') c = ' ';

  std::istringstream iss(line);
  std::string index, name, type, addr_s, off_s, size_s;
  if (!(iss >> index >> name >> type >> addr_s >> off_s >> size_s)) return r;

  r.start  = std::stoull(addr_s, nullptr, 16);
  r.offset = std::stoull(off_s,  nullptr, 16);
  r.size   = std::stoull(size_s, nullptr, 16);
  r.valid  = true;
  return r;
}

// .rodata 범위 안 + 문자열이면 true
bool isRodataString(const std::string &binary, const RodataRange &r,
                    uint64_t val) {
  if (!r.valid) return false;
  if (val < r.start || val >= r.start + r.size) return false;

  uint64_t file_off = r.offset + (val - r.start);
  std::ifstream f(binary, std::ios::binary);
  if (!f.is_open()) return false;
  f.seekg(file_off);

  const int MAX = 256;
  bool terminated = false;
  int count = 0;
  for (int i = 0; i < MAX; i++) {
    int ch = f.get();
    if (ch == EOF) break;
    if (ch == 0) { terminated = true; break; }
    unsigned char uc = (unsigned char)ch;
    if (!(std::isprint(uc) || uc == '\t' || uc == '\n')) return false;
    count++;
  }
  return terminated && count > 0;
}

// 특정 전역 주소(addr)가 IR에서 inttoptr(addr to Ty*) 형태로 쓰인 곳을 찾아
// pointee 타입(Ty)을 반환. 못 찾으면 nullptr.
llvm::Type *findGlobalPointeeTypeFromIR(llvm::Function &F, int64_t addr) {
  for (llvm::BasicBlock &BB : F) {
    for (llvm::Instruction &I : BB) {
      for (llvm::Value *op : I.operands()) {
        auto *ce = llvm::dyn_cast<llvm::ConstantExpr>(op);
        if (!ce || ce->getOpcode() != llvm::Instruction::IntToPtr) continue;

        auto *ci = llvm::dyn_cast<llvm::ConstantInt>(ce->getOperand(0));
        if (!ci || ci->getSExtValue() != addr) continue;

        return ce->getType()->getPointerElementType();
      }
    }
  }
  return nullptr;
}

} // namespace

// -------------------------
// 유틸리티
// -------------------------

static std::string last_two_chars(const std::string &s) {
  if (s.size() < 2) return s;
  return s.substr(s.size() - 2);
}

// -------------------------
// TypeGraph 생성자
// -------------------------

TypeGraph::TypeGraph(Function &F, const PointsToGraph &ptg, VarRecover &vr)
    : PointsToGraph(ptg), vr_(vr) {
  for (auto &pair : ptr_graph) {
    const Node &offset = pair.first;
    const std::set<Node> &successors = pair.second;

    if (offset.getType() == NodeType::Const) {
      continue;
    }

    nodes.insert(offset);
    edges[offset];
    for (const Node &succ : successors)
      edges[offset].insert(succ);

    types[offset] = TypeLattice::unknown();
  }
}

// 슬롯 offset이 가리키는 const_i32가 전부 .rodata 문자열 주소인지 검사
// bool TypeGraph::isAllRodataString(Function &F, const std::string &offset) {
//   const std::string binary = "/home/yujina/elis/pass/binary";
//   static RodataRange rodata = getRodataRange(binary);  // 1회만 읽음

//   if (!vr_.offset_vars_map_.count(offset)) return false;

//   bool found_const = false;
//   for (const std::string &var : vr_.offset_vars_map_[offset]) {
//     Instruction *def = vr_.GetDef(F, var);
//     if (!def) continue;

//     // 이 var를 pointer operand로 쓰는 store들의 value 검사
//     for (User *u : def->users()) {
//       auto *store = dyn_cast<StoreInst>(u);
//       if (!store) continue;
//       if (store->getPointerOperand() != def) continue;

//       Value *val = store->getValueOperand();
//       auto *ci = dyn_cast<ConstantInt>(val);
//       if (!ci) continue;  // ConstantInt 아닌 store(offset 등)는 무시

//       found_const = true;
//       uint64_t v = ci->getZExtValue();
//       // 하나라도 .rodata 문자열이 아니면 즉시 실패 (= "전부" 조건)
//       if (!isRodataString(binary, rodata, v))
//         return false;
//     }
//   }

//   // ConstantInt store가 하나라도 있었고, 전부 통과했을 때만 true
//   return found_const;
// }
bool TypeGraph::isAllRodataString(Function &F, const std::string &offset) {
  const std::string binary = "/home/yujina/elis/pass/binary";
  static RodataRange rodata = getRodataRange(binary);

  if (!vr_.offset_vars_map_.count(offset)) return false;

  for (const std::string &var : vr_.offset_vars_map_[offset]) {
    Instruction *def = vr_.GetDef(F, var);
    if (!def) continue;

    for (User *u : def->users()) {
      auto *store = dyn_cast<StoreInst>(u);
      if (!store) continue;
      if (store->getPointerOperand() != def) continue;

      Value *val = store->getValueOperand();
      auto *ci = dyn_cast<ConstantInt>(val);
      if (!ci) continue;

      uint64_t v = ci->getZExtValue();
      if (isRodataString(binary, rodata, v))
        return true;   // ← 하나라도 문자열이면 즉시 true
    }
  }
  return false;
}


// -------------------------
// 타입 초기화 및 전파
// -------------------------

void TypeGraph::initType(Function &F) {
  LLVMContext &ctx = F.getContext();
  Type *ty = Type::getInt32Ty(ctx);

  // 각 Local 슬롯이 const_i32를 가리키고, 그 슬롯의 ConstantInt store가
  // 전부 .rodata 문자열 주소면 const_str 엣지로 교체
  Node const_i32_node{"const_i32", NodeType::Const};
  Node const_str_node{"const_str", NodeType::Const};
  bool need_const_str = false;

  for (auto &pair : edges) {
    Node slot = pair.first;
    if (slot.getType() != NodeType::Local) continue;

    std::set<Node> &succs = pair.second;
    if (succs.find(const_i32_node) == succs.end()) continue;  // const_i32 안 가리키면 skip

    if (isAllRodataString(F, slot.getName())) {
      succs.erase(const_i32_node);
      succs.insert(const_str_node);
      need_const_str = true;
    }
  }

  if (need_const_str) {
    nodes.insert(const_str_node);
    // types[const_str_node] = TypeLattice::unknown();  // 아래 시딩 루프에서 i8* 부여
    types[const_str_node] = TypeLattice::concrete(Type::getInt8Ty(ctx)->getPointerTo());
  }

  // 1. Const 노드에 타입 부여
  for (auto &pair : edges) {
    Node n = pair.first;
    if (n.getType() == NodeType::Const) {
      std::string name = n.getName();
      std::string type_str = name.substr(name.find('_') + 1);
      Type *const_ty = nullptr;
      if (type_str == "i8") {
        const_ty = Type::getInt8Ty(ctx);
      } else if (type_str == "str") {
        const_ty = Type::getInt8Ty(ctx)->getPointerTo();  // i8*
      } else if (type_str == "i32"){
        const_ty = Type::getInt32Ty(ctx);
      }else{
        llvm::report_fatal_error("[typing] unknown type");
      }
      types[n] = TypeLattice::concrete(const_ty);
    }
  }

  // Array 노드에 원소 타입 시딩
  seedArrayNodeTypes(F);

  // 2. 1차 fixpoint
  runToFixpoint();

  // 3. 타입 미결정 leaf 노드 수집
  std::set<Node> untyped_leaf;
  for (auto &pair : types) {
    Node current = pair.first;
    if (current.getType() == NodeType::Bitcast) continue;
    if (pair.second.isUnknown() && getEdgeSize(current) == 0)
      untyped_leaf.insert(current);
  }

  // 4. 각 leaf에 타입을 시도해보고 안전하면 적용
  // for (Node untyped : untyped_leaf) {
  //   std::map<Node, TypeLattice> temp_types = types;
  //   types[untyped] = TypeLattice::concrete(ty);
  //   bool result = checkLeafTypeisOk(untyped);
  //   types = temp_types;
  //   if (result)
  //     types[untyped] = TypeLattice::concrete(ty->getPointerTo());
  // }
  for (Node untyped : untyped_leaf) {
    std::map<Node, TypeLattice> temp_types = types;
    Type *leaf_ty = getLeafNodeType(F, untyped.getName()); // 여기 수정
    types[untyped] = TypeLattice::concrete(leaf_ty);
    bool result = checkLeafTypeisOk(untyped);
    types = temp_types;
    if (result)
      types[untyped] = TypeLattice::concrete(leaf_ty->getPointerTo());
  }

  runToFixpoint();
  outs() << "exit\n";
}

// uninitialized leaf 노드(succ 없는 Local 노드)에 const_i32 엣지 추가
void TypeGraph::addConstToUninitNodes() {
  Node const_i32_node{"const_i32", NodeType::Const};

  for (auto &pair : edges) {
    Node n = pair.first;
    if (n.getType() != NodeType::Local && n.getType() != NodeType::Global) continue;
    if (vr_.array_info_map_.count(n.getName())) continue; 
    
    // succ가 하나도 없으면 uninitialized leaf
    if (pair.second.empty()) {
      pair.second.insert(const_i32_node);
    }
  }
}

void TypeGraph::typingCycle() {
  // step 1: succ으로부터 typing
  for (auto &pair : types) {
    Node current = pair.first;
    if (current.getType() == NodeType::Const) continue;
    TypeLattice current_ty = pair.second;

    if (current_ty.isUnknown()) {
      std::set<Node> succs = edges[current];
      bool check = false;
      std::set<Type *> succ_types;
      Type *succ_ty = nullptr;

      for (Node succ : succs) {
        if (succ.getType() == NodeType::Bitcast) continue;
        if (types[succ].isConcrete()) {
          check = true;
          succ_types.insert(types[succ].ty);
          succ_ty = types[succ].ty;
        }
      }

      if (check) {
        if (succ_types.size() != 1)
          llvm::report_fatal_error("[typing] succ type diff");
        types[current] = TypeLattice::concrete(succ_ty->getPointerTo());
      }
    }
  }

  // step 2: pred가 typed면 succ에서 가져옴
  for (auto &pair : types) {
    Node current = pair.first;
    if (current.getType() == NodeType::Const) continue;
    TypeLattice current_ty = pair.second;

    if (current_ty.isConcrete()) {
      for (Node succ : edges[current]) {
        if (succ.getType() == NodeType::Bitcast) continue;
        if (types[succ].isUnknown())
          types[succ] = TypeLattice::concrete(current_ty.ty->getPointerElementType());
      }
    }
  }
}

void TypeGraph::runToFixpoint() {
  bool changed = true;
  while (changed) {
    changed = false;
    std::map<Node, TypeLattice> t1 = types;
    typingCycle();
    std::map<Node, TypeLattice> t2 = types;

    if (t1.size() != t2.size())
      llvm::report_fatal_error("type graph size diff after cycle");

    for (auto &pair : t2) {
      if (!TypeLattice::order(pair.second, t1[pair.first])) {
        changed = true;
        break;
      }
    }
  }
}

void TypeGraph::seedArrayNodeTypes(Function &F) {
  LLVMContext &ctx = F.getContext();

  for (auto &pair : edges) {
    Node n = pair.first;
    if (n.getType() != NodeType::Local) continue;
    if (!vr_.array_info_map_.count(n.getName())) continue;

    if (getEdgeSize(n) > 0) {
      llvm::report_fatal_error(
          ("[typing] array node has unexpected out-edges: " + n.getName())
              .c_str());
    }

    ArrayInfo &info = vr_.array_info_map_[n.getName()];
    Type *elem_ty = TypeStrToLLVMType(ctx, info.type);  // 이제 정상 호출됨
    types[n] = TypeLattice::concrete(elem_ty);
  }
}

bool TypeGraph::propagateUp(Node n) {
  std::map<Node, std::set<Node>> preds = getPredMap(edges);
  Type *node_ty = types[n].ty;

  for (Node pred : preds[n]) {
    TypeLattice pred_ty = types[pred];
    if (pred_ty.isConcrete()) {
      if (node_ty->getPointerTo() != types[pred].ty)
        return false;
    } else {
      types[pred] = TypeLattice::concrete(node_ty->getPointerTo());
      if (!propagateUp(pred))
        return false;
    }
  }
  return true;
}

bool TypeGraph::propagateDown(Node n) {
  Type *node_ty = types[n].ty;
  for (Node succ : edges[n]) {
    if (succ.isBitcast()) continue;
    TypeLattice succ_ty = types[succ];
    if (succ_ty.isUnknown()) {
      if (!node_ty->isPointerTy()) return false;
      types[succ] = TypeLattice::concrete(node_ty->getPointerElementType());
      if (!propagateDown(succ)) return false;
    }
  }
  return true;
}

bool TypeGraph::checkLeafTypeisOk(Node n) {
  return propagateUp(n) && propagateDown(n);
}

// -------------------------
// 사이클 제거
// -------------------------

void TypeGraph::removeCycle() {
  while (removeCycleFunc()) {}
}

bool TypeGraph::removeCycleFunc() {
  for (auto &pair : edges) {
    Node n = pair.first;

    std::stack<Node> stack;
    std::map<Node, int> visited;
    std::map<Node, bool> in_stack;

    stack.push(n);
    while (!stack.empty()) {
      Node current = stack.top();

      if (visited[current] == 0) {
        visited[current] = 1;
        in_stack[current] = true;

        bool pushed = true;
        for (Node next : edges[current]) {
          if (next.getType() == NodeType::Bitcast) continue;
          if (visited[next] == 0) {
            stack.push(next);
            pushed = true;
          } else if (in_stack[next]) {
            addBitCastEdge(current, next);
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

void TypeGraph::addBitCastEdge(Node source, Node dest) {
  std::string source_name = last_two_chars(source.getName());
  std::string dest_name = last_two_chars(dest.getName());
  std::string new_source_name = source_name + "_" + dest_name + "_bitcast";

  std::set<Node> &succ = edges[source];
  succ.erase(dest);

  Node new_bitcast_node{new_source_name, NodeType::Bitcast};
  types[new_bitcast_node] = TypeLattice::unknown();
  edges[source].insert(new_bitcast_node);
  edges[new_bitcast_node].insert(Node{dest.getName(), NodeType::Local});
}

// -------------------------
// 다중 경로 제거
// -------------------------

void TypeGraph::removeOutEdgeMismatch() {
  while (removeOutEdgeMismatchFunc()) {}
}

bool TypeGraph::removeOutEdgeMismatchFunc() {
  for (auto &pair : edges) {
    Node slot = pair.first;
    if (slot.getType() != NodeType::Local && slot.getType() != NodeType::Global) 
      continue;

    std::set<Node> &succs = pair.second;

    bool has_nonptr_const = false;
    bool has_offset = false;
    for (const Node &s : succs) {
      if (s.getType() == NodeType::Const) {
        std::string suffix = s.getName().substr(s.getName().find('_') + 1);
        if (suffix == "i32" || suffix == "i8")
          has_nonptr_const = true;
      } else if (s.getType() == NodeType::Local || s.getType() == NodeType::Global) {
        has_offset = true;
      }
    }

    if (has_nonptr_const && has_offset) {
      std::vector<Node> to_split;
      for (const Node &s : succs) {
        if (s.getType() == NodeType::Const) {
          std::string suffix = s.getName().substr(s.getName().find('_') + 1);
          if (suffix == "i32" || suffix == "i8")
            to_split.push_back(s);
        }
      }
      for (const Node &c : to_split)
        addBitCastEdge(slot, c);
      return true;
    }
  }
  return false;
}


void TypeGraph::removeMultiPath() {
  while (removeMultiPathFunc()) {}
}

bool TypeGraph::removeMultiPathFunc() {
  calculatedDistance();

  std::map<Node, std::set<Node>> pred_edge_map = getPredMap(edges);
  std::set<Node> in_edge_morethan_2;
  for (auto &pair : pred_edge_map) {
    if (pair.second.size() >= 2)
      in_edge_morethan_2.insert(pair.first);
  }

  if (in_edge_morethan_2.empty()) return false;

  for (Node n : in_edge_morethan_2) {
    if (n.getType() == NodeType::Const || n.getType() == NodeType::Null) continue;

    std::set<Node> preds = pred_edge_map[n];

    // pred들 사이의 거리를 직접 비교
    // 기준: 각 pred에서 n까지의 거리(= 1로 고정)가 아니라
    // pred들끼리의 거리를 비교해서 경로 깊이가 다른지 확인
    int max_dist = 0;
    for (Node pred : preds)
      for (Node other_pred : preds)
        if (pred != other_pred)
          max_dist = std::max(max_dist, distance[pred][other_pred]);

    std::set<Node> node_set;
    for (Node pred : preds)
      for (Node other_pred : preds)
        if (pred != other_pred && distance[pred][other_pred] != max_dist)
          node_set.insert(pred);

    if (!node_set.empty()) {
      for (Node src : node_set)
        addBitCastEdge(src, n);
      return true;
    }
  }
  return false;
}

void TypeGraph::calculatedDistance() {
  for (Node i : nodes)
    for (Node j : nodes)
      distance[i][j] = INT_MAX;

  for (auto &pair : edges) {
    Node src = pair.first;
    for (Node dst : pair.second)
      distance[src][dst] = 1;
  }

  for (Node k : nodes) {
    distance[k][k] = 0;
    for (Node i : nodes) {
      for (Node j : nodes) {
        if (distance[i][k] != INT_MAX && distance[k][j] != INT_MAX) {
          distance[i][j] = std::min(distance[i][j],
                                    distance[i][k] + distance[k][j]);
        }
      }
    }
  }
}

void TypeGraph::printDistance() {
  std::vector<Node> node_list(nodes.begin(), nodes.end());

  outs() << "\n=== Distance Matrix ===\n";

  // 헤더
  outs() << "                ";
  for (const Node &j : node_list)
    outs() << j.getName() << " | ";
  outs() << "\n";

  // 각 행
  for (const Node &i : node_list) {
    outs() << i.getName() << " | ";
    for (const Node &j : node_list) {
      int d = distance[i][j];
      if (d == INT_MAX)
        outs() << "INF | ";
      else
        outs() << d << " | ";
    }
    outs() << "\n";
  }
  outs() << "======================\n\n";
}

// -------------------------
// 유틸리티
// -------------------------

std::map<Node, std::set<Node>>
TypeGraph::getPredMap(std::map<Node, std::set<Node>> edges) {
  std::map<Node, std::set<Node>> preds;
  for (auto &pair : edges) {
    Node current_node = pair.first;
    if (current_node.getType() == NodeType::Bitcast) continue;
    for (Node succ : pair.second)
      preds[succ].insert(current_node);
  }
  return preds;
}

int TypeGraph::getEdgeSize(Node current) {
  int size = edges[current].size();
  for (Node succ : edges[current]) {
    if (succ.getType() == NodeType::Bitcast)
      size--;
  }
  return size;
}

llvm::Type *TypeGraph::getLeafNodeType(Function &F, std::string offset) {
  LLVMContext &ctx = F.getContext();

  // offset이 사실 전역변수 이름(gv_N)인 경우: IR에서 이 주소가
  // 실제로 캐스팅된 포인터 타입을 찾아 pointee 타입을 반환
  for (const auto &pair : vr_.global_var_map_) {
    if (pair.second != offset) continue;
    if (Type *found = findGlobalPointeeTypeFromIR(F, pair.first))
      return found;
    break;  // 이름은 매칭됐지만 IR에서 못 찾음 -> 아래 fallback으로
  }

  if (!vr_.offset_vars_map_.count(offset))
    return Type::getInt32Ty(ctx);

  for (const std::string &var : vr_.offset_vars_map_[offset]) {
    Instruction *def = vr_.GetDef(F, var);
    if (!def) continue;

    if (auto *itp = dyn_cast<IntToPtrInst>(def)) {
      return itp->getType()->getPointerElementType();
    }

    for (User *u : def->users()) {
      if (auto *store = dyn_cast<StoreInst>(u)) {
        if (store->getPointerOperand() == def) {
          return store->getValueOperand()->getType();
        }
      }
    }
  }

  return Type::getInt32Ty(ctx);
}

std::map<Node, TypeLattice> TypeGraph::getTypes() { return types; }

// -------------------------
// DOT 출력
// -------------------------

void TypeGraph::exportToDot(const std::string &filename) {
  std::ofstream file(filename);
  if (!file.is_open()) {
    outs() << "Error: Unable to open file " << filename << "\n";
    return;
  }

  file << "digraph G {\n";
  for (const auto &pair : edges) {
    const Node src = pair.first;
    const auto &dests = pair.second;

    if (dests.empty()) {
      file << "  \"" << types[src].str() << " " << src.getName() << "\";\n";
    } else {
      for (const auto &dest : dests) {
        std::string style = dest.getType() == NodeType::Bitcast
                                ? "[style=dotted]"
                                : "";
        file << "  \"" << types[src].str() << " " << src.getName()
             << "\" -> \"" << types[dest].str() << " " << dest.getName()
             << "\"" << style << ";\n";
      }
    }
  }
  file << "}\n";
  file.close();
  outs() << "Type Graph exported to " << filename << "\n";
}
