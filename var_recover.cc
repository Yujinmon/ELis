#include "var_recover.h"

#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <nlohmann/json.hpp>
#include <fstream>
#include <string>
#include <algorithm>
#include <sstream>

using json = nlohmann::json;
using namespace llvm;

// -------------------------
// 유틸리티 (파일 내부)
// -------------------------

static int64_t HexToDecimal(std::string hex) {
  std::string cleaned = hex;
  if (cleaned.substr(0, 2) == "0x")
    cleaned = cleaned.substr(2);
  else if (cleaned[0] == 'x')
    cleaned = cleaned.substr(1);

  uint32_t unsignedVal = 0;
  std::stringstream ss;
  ss << std::hex << cleaned;
  ss >> unsignedVal;
  return static_cast<int64_t>(static_cast<int32_t>(unsignedVal));
}

// -------------------------
// Helper
// -------------------------

Type* VarRecover::GetActualTypeFromIntToPtr(Function& F, const std::string& offset) {
  LLVMContext &ctx = F.getContext();
  
  if (!offset_vars_map_.count(offset))
    return Type::getInt32Ty(ctx); // fallback
  
  for (const std::string &var : offset_vars_map_[offset]) {
    Instruction *def = GetDef(F, var);
    if (!def) continue;
    
    // inttoptr이면 dest 타입 바로 읽기
    if (auto *itp = dyn_cast<IntToPtrInst>(def)) {
      Type *ptr_ty = itp->getType();           // ex) i8*
      return ptr_ty->getPointerElementType();  // ex) i8
    }
  }
  return Type::getInt32Ty(ctx); // fallback
}

int TypeStrToByteSize(const std::string &type_str) {
  if (type_str == "i8")  return 1;
  if (type_str == "i16") return 2;
  if (type_str == "i32") return 4;
  if (type_str == "i64") return 8;
  llvm::report_fatal_error(
      ("[stack_shape] unknown array type: " + type_str).c_str());
}

llvm::Type* TypeStrToLLVMType(llvm::LLVMContext &ctx,
                                      const std::string &type_str) {
  if (type_str == "i8")  return Type::getInt8Ty(ctx);
  if (type_str == "i16") return Type::getInt16Ty(ctx);
  if (type_str == "i32") return Type::getInt32Ty(ctx);
  if (type_str == "i64") return Type::getInt64Ty(ctx);
  llvm::report_fatal_error(
      ("[stack_shape] unknown array type: " + type_str).c_str());
}

// -------------------------
// SetGlobalVarMap
// -------------------------

void VarRecover::SetGlobalVarMap() {
  std::ifstream file("/home/yujina/elis/pass/globals.json");
  if (!file.is_open()) {
    outs() << "globals.json file error\n";
    return;
  }

  json json_data;
  file >> json_data;
  file.close();

  if (!json_data.contains("globals") || !json_data["globals"].is_array()) {
    outs() << "error: \"globals\" array not found in globals.json\n";
    return;
  }

  int idx = 1;
  for (const json &addr_json : json_data["globals"]) {
    if (!addr_json.is_number_integer()) continue;

    int64_t addr = addr_json.get<int64_t>();
    std::string name = "gv_" + std::to_string(idx);

    global_var_map_[addr] = name;
    global_name_addr_map_[name] = addr;
    ++idx;
  }
}

// -------------------------
// GetGlobalVarMap
// -------------------------

std::map<int64_t, std::string> VarRecover::GetGlobalVarMap() {
  return global_var_map_;
}


// -------------------------
// GetVarName / GetDef
// -------------------------

std::string VarRecover::GetVarName(Function &F, Value *I) {
  std::string inst;
  llvm::raw_string_ostream(inst) << *I;
  std::string inst_name = inst.substr(0, inst.find("=") - 1);
  inst_name.erase(inst_name.begin(),
                  std::find_if(inst_name.begin(), inst_name.end(),
                               [](unsigned char ch) { return !std::isspace(ch); }));
  return inst_name;
}

Instruction *VarRecover::GetDef(Function &F, std::string name) {
  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      std::string inst;
      llvm::raw_string_ostream(inst) << I;
      std::string inst_name = inst.substr(0, inst.find("=") - 1);
      inst_name.erase(inst_name.begin(),
                      std::find_if(inst_name.begin(), inst_name.end(),
                                   [](unsigned char ch) { return !std::isspace(ch); }));
      if (inst_name == name)
        return &I;
    }
  }
  return nullptr;
}

// -------------------------
// SetSymexMap
// -------------------------

void VarRecover::SetSymexMap(Function &F) {
  std::ifstream file("/home/yujina/elis/pass/symex.json");
  if (!file.is_open()) {
    outs() << "symex.json file error\n";
    return;
  }

  json json_data;
  file >> json_data;
  file.close();

  for (auto it = json_data.begin(); it != json_data.end(); ++it) {
    const std::string key = it.key();
    const json &val = it.value();

    if (key.empty()) continue;

    size_t sharp_pos = key.find('#');
    if (sharp_pos == std::string::npos || sharp_pos + 1 >= key.size()) continue;

    std::string hex = key.substr(sharp_pos + 1);
    if (hex.empty()) {
      outs() << "error in getting hex from symex result\n";
      continue;
    }

    if (!val.is_array()) continue;

    for (const json &entry : val) {
      if (!entry.is_object()) continue;
      auto var_it = entry.find("var");
      if (var_it == entry.end() || !var_it->is_string()) continue;

      const std::string var = var_it->get<std::string>();
      // Instruction *ori_var = GetDef(F, var);
      // if (!ori_var) continue;

      offset_vars_map_[hex].insert(var);
      var_offset_map_[var] = hex;
    }
  }
}

// -------------------------
// SetStackLayoutMap
// -------------------------
void VarRecover::SetStackLayoutMap() {
  std::ifstream file("/home/yujina/elis/pass/stack_shape.json");
  json json_data;
  file >> json_data;
  file.close();

  for(const auto& v : json_data["variables"]) {
    VariableInfo info;
    info.offset = v["offset"].get<std::string>().substr(1);
    info.start = v["start"];
    info.end = v["end"];
    variable_infos_.push_back(info);
  }

  for(const auto& v : json_data["arrays"]) {
    ArrayInfo info;
    info.offset = v["offset"].get<std::string>().substr(1);
    info.start = v["start"];
    info.end = v["end"];
    info.size = v["size"];
    info.type = v["type"].get<std::string>();
    info.element_size = TypeStrToByteSize(info.type);

    // sanity check (선택)
    if (info.size * info.element_size != info.end - info.start) {
      outs() << "[WARN] array size/element_size mismatch at offset "
             << info.offset << "\n";
    }

    array_infos_.push_back(info);
    array_info_map_[info.offset] = info;
  }
}


llvm::GlobalVariable *VarRecover::MakeGlobalAlloca(Module &M, const std::string &gv_name, llvm::Type *ty) {
  LLVMContext &ctx = M.getContext();

  return new GlobalVariable(
      M,                                  // 소속 Module (F.getParent()로 얻음)
      ty,                                 // 타입
      /*isConstant=*/false,
      GlobalValue::InternalLinkage,       // 이 모듈 안에서만 쓰임 -> Internal
      Constant::getNullValue(ty),         // 초기값 (필수! 없으면 declaration이 되어 store 불가)
      gv_name                             // 이름 (예: "gv_1")
  );
}

// -------------------------
// MakeAlloca
// -------------------------

void VarRecover::MakeAlloca(Function &F) {
  LLVMContext& ctx = F.getContext();
  PointsToGraph points_to_graph;
  PointsToGraphOp points_to_graph_op;

  points_to_graph_op.initGraph(points_to_graph, offset_vars_map_, global_var_map_);
  points_to_graph_op.makePointsToGraph(points_to_graph, F, var_offset_map_, global_var_map_);
  points_to_graph_op.exportToDot(points_to_graph, "visualize/PointsToGraph.dot");

  TypeGraph type_graph(F, points_to_graph, *this);
  type_graph.addConstToUninitNodes();
  type_graph.removeCycle();
  type_graph.removeMultiPath();
  type_graph.removeOutEdgeMismatch();
  type_graph.initType(F);
  type_graph.exportToDot("visualize/typegraph.dot");

  BasicBlock &entryBB = F.getEntryBlock();
  IRBuilder<> builder(&entryBB, entryBB.begin());

  for (auto &pair : type_graph.getTypes()) {
    Node offset = pair.first;
    TypeLattice offset_ty = pair.second;

    if (offset.getType() == NodeType::Null ||
        offset.getType() == NodeType::Const)
      continue;

    if (offset.getType() == NodeType::Global && offset_ty.isConcrete()) {
      Module *M = F.getParent();
      Type *var_ty = offset_ty.ty->getPointerElementType();

      GlobalVariable *new_gv = MakeGlobalAlloca(*M, offset.getName(), var_ty);

      int64_t addr = global_name_addr_map_[offset.getName()];
      addr_global_map_[addr] = new_gv;                          

      offset_global_map_[offset.getName()] = new_gv;   // 새 맵
      for (std::string var : offset_vars_map_[offset.getName()])
        var_global_map_[var] = new_gv;                 // 새 맵

      outs() << "NEW GLOBAL: " << *new_gv << "\n";
      continue;
    }

    if (offset.getType() == NodeType::Local && offset_ty.isConcrete()) {
      std::set<std::string> vars = offset_vars_map_[offset.getName()];
      AllocaInst* new_alloca = nullptr;

      // offset이 array라서 map에 존재하면..
      if(array_info_map_.count(offset.getName())) {
        ArrayInfo info = array_info_map_[offset.getName()];
        Type* elem_ty = offset_ty.ty;   // 그래프가 시딩한 원소 타입 그대로 사용
        ArrayType* arr_ty = ArrayType::get(elem_ty, info.size);
        new_alloca = builder.CreateAlloca(arr_ty, nullptr, offset.getName());
      // } else {
      //   // 아닐 경우 변수 선언
      //   Type* var_ty = offset_ty.ty->getPointerElementType();
      //   new_alloca = builder.CreateAlloca(var_ty, nullptr, offset.getName());
      // }
      } else {
        Type* var_ty;

        // 이 노드가 배열 offset을 직접 가리키는 경우 (예: xffffffd4 -> xffffffe4)
        // offset_ty.ty는 이미 "원소 타입에 대한 포인터"로, 한 번 더 벗기면 안 됨
        bool points_to_array = false;
        for (const Node &succ : type_graph.getEdges(offset)) {
          if (array_info_map_.count(succ.getName())) {
            points_to_array = true;
            break;
          }
        }

        if (points_to_array) {
          var_ty = offset_ty.ty;
        } else {
          var_ty = offset_ty.ty->getPointerElementType();
        }

        new_alloca = builder.CreateAlloca(var_ty, nullptr, offset.getName());
      }
      
      // offset을 이름으로 선언한 alloca와 offset과의 mapping
      offset_alloca_map_[offset.getName()] = new_alloca;
      for(std::string var : vars) {
        var_alloca_map_[var] = new_alloca;
      }

      // Type *var_ty = offset_ty.ty->getPointerElementType();
      // std::set<std::string> vars = offset_vars_map_[offset.getName()];

      // AllocaInst *new_alloca =
      //     builder.CreateAlloca(var_ty, nullptr, offset.getName());

      // offset_alloca_map_[offset.getName()] = new_alloca;
      // for (std::string var : vars)
      //   var_alloca_map_[var] = new_alloca;
    }
  }

  ReplaceUsesOfVar(F, type_graph);
  ReplaceArrayVarinLoop(F);
  ReplaceArrayBaseAliasVars(F);
  ReplaceGlobalUses(F, type_graph);
}

// -------------------------
// ReplaceUseofPointerVar
// -------------------------

void VarRecover::ReplaceUseofPointerVar(Function &F, TypeGraph &type_graph,
                                        std::string var) {
  AllocaInst *alloca_inst = var_alloca_map_[var];
  Instruction *def = GetDef(F, var);
  std::vector<Instruction *> trash_can;

  for (User *u : def->users()) {
    if (Instruction *user_inst = dyn_cast<Instruction>(u)) {
      IRBuilder<> builder(user_inst);

      /*
        STORE INST
      */
      if (auto *store_inst = dyn_cast<StoreInst>(user_inst)) {
        Value *dest = store_inst->getValueOperand();
        Value *source = store_inst->getPointerOperand();
        std::string dest_var_name = GetVarName(F, dest);
        std::string source_var_name = GetVarName(F, source);

        std::string dest_offset = var_offset_map_[dest_var_name];
        std::string source_offset = var_offset_map_[source_var_name];
        AllocaInst *dest_alloca_inst = var_alloca_map_[dest_var_name];
        AllocaInst *source_alloca_inst = var_alloca_map_[source_var_name];
        std::set<Node> succs = type_graph.getEdges(source_offset);

        bool replaced = false;

        // 1) store {offset}, {offset}
        if (succs.find(Node{dest_offset, NodeType::Local}) != succs.end()) {
          Value *dest_val = dest_alloca_inst;

          // dest가 배열이면: 배열 전체 포인터가 아니라 0번째 원소 주소로 변환 (decay)
          if (dest_alloca_inst->getAllocatedType()->isArrayTy()) {
            dest_val = builder.CreateGEP(
                dest_alloca_inst->getAllocatedType(),
                dest_alloca_inst,
                {ConstantInt::get(Type::getInt32Ty(F.getContext()), 0),
                ConstantInt::get(Type::getInt32Ty(F.getContext()), 0)},
                "arr_decay");
          }

          builder.CreateStore(dest_val, source_alloca_inst);
          replaced = true;
        }
        // 2) store {const}, {offset}
        else if (isa<ConstantInt>(dest)) {
          Type *elem_ty = source_alloca_inst->getAllocatedType();
          Value *to_store = nullptr;

          if (elem_ty->isPointerTy()) {
            // 상수(주소)를 포인터 슬롯에: inttoptr
            to_store = builder.CreateIntToPtr(dest, elem_ty, "const_to_ptr");
          } else if (elem_ty->isIntegerTy()) {
            // 정수 슬롯: 폭이 같다고 가정, 다르면 예외
            if (elem_ty != dest->getType())
              llvm::report_fatal_error(
                  "[ReplaceUseofPointerVar] const store width mismatch");
            to_store = dest;
          } else {
            llvm::report_fatal_error(
                "[ReplaceUseofPointerVar] unexpected elem type for const store");
          }

          builder.CreateStore(to_store, source_alloca_inst);
          replaced = true;
        }
        // 3) bitcast: 그래프가 실제로 확인해준 관계일 때만 처리
        else {
          for (Node succ : succs) {
            if (succ.getType() != NodeType::Bitcast) continue;

            for (auto &p : type_graph.getEdges(succ)) {
              if (p.getName() != dest_offset) continue;

              Type *bitcast_type = type_graph.getNodeType(succ.getName());
              Value *bitcast_inst = builder.CreateBitCast(
                  source_alloca_inst, bitcast_type, succ.getName());
              builder.CreateStore(dest_alloca_inst, bitcast_inst, "store");
              replaced = true;
            }
          }
        }

        // 그래프/타입 근거로 대체하지 못했으면 원본 store를 그대로 남기고
        // trash_can에 넣지 않는다 (데이터 유실 방지)
        if (replaced) {
          trash_can.push_back(store_inst);
        } else {
          outs() << "[ReplaceUseofPointerVar] skip store (no matching relation): "
                 << *store_inst << "\n";
        }
      }

      /*
        PHI INST
      */
      if (auto* phi_inst = dyn_cast<PHINode>(user_inst)) {
        if (alloca_inst != nullptr) {
          Instruction* split_point = phi_inst->getParent()->getFirstNonPHI();

          BasicBlock* origin_bb = phi_inst->getParent();
          BasicBlock* new_bb = origin_bb->splitBasicBlock(split_point, origin_bb->getName() + ".split");

          Instruction* term = origin_bb->getTerminator();
          IRBuilder<> split_builder(term);

          Type* alloca_ty = alloca_inst->getType()->getPointerElementType();
          Value* new_load = split_builder.CreateLoad(alloca_ty, alloca_inst, "phi_load");

          phi_inst->replaceAllUsesWith(new_load);
          // trash_can.push_back(phi_inst);
        }
      }
    }
  }

  for (Instruction *i : trash_can)
    i->eraseFromParent();
}

void VarRecover::ReplaceUseOfGlobalVar(Function &F, int64_t addr, GlobalVariable *gv) {
  // 먼저 교체 대상만 수집 (순회 중 operand를 바꾸면 안전하지 않으므로)
  std::vector<std::pair<Instruction*, unsigned>> ptr_uses;  // inttoptr(addr) 형태
  std::vector<std::pair<Instruction*, unsigned>> int_uses;  // bare addr 정수 형태

  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      for (unsigned i = 0; i < I.getNumOperands(); ++i) {
        Value *op = I.getOperand(i);

        if (auto *ce = dyn_cast<ConstantExpr>(op)) {
          if (ce->getOpcode() != Instruction::IntToPtr) continue;
          auto *ci = dyn_cast<ConstantInt>(ce->getOperand(0));
          if (ci && ci->getSExtValue() == addr)
            ptr_uses.push_back({&I, i});
        } else if (auto *ci = dyn_cast<ConstantInt>(op)) {
          if (ci->getSExtValue() == addr)
            int_uses.push_back({&I, i});
        }
      }
    }
  }

  // 1) 포인터 문맥: inttoptr(addr to Ty*) -> gv (타입 다르면 bitcast)
  for (auto &use : ptr_uses) {
    Instruction *inst = use.first;
    unsigned idx = use.second;

    Type *expected_ptr_ty = inst->getOperand(idx)->getType();
    Value *replacement = gv;
    if (gv->getType() != expected_ptr_ty)
      replacement = ConstantExpr::getBitCast(gv, expected_ptr_ty);

    inst->setOperand(idx, replacement);
  }

  // 2) 정수 문맥: bare ADDR (다른 gv의 데이터로 저장되는 주소값) -> ptrtoint(gv)
  for (auto &use : int_uses) {
    Instruction *inst = use.first;
    unsigned idx = use.second;

    Type *expected_int_ty = inst->getOperand(idx)->getType();
    Constant *replacement = ConstantExpr::getPtrToInt(gv, expected_int_ty);
    inst->setOperand(idx, replacement);
  }
}

void VarRecover::ReplaceGlobalUses(Function &F, TypeGraph &type_graph) {
  // 1) global-to-global(포인터 관계) store부터 우선 처리
  ReplaceGlobalStoreEdges(F, type_graph);

  // 2) 남은 순수 값(주소 리터럴) 치환
  for (auto &pair : addr_global_map_) {
    ReplaceUseOfGlobalVar(F, pair.first, pair.second);
  }
}

void VarRecover::ReplaceGlobalStoreEdges(Function &F, TypeGraph &type_graph) {
  std::vector<Instruction *> trash_can;

  for (BasicBlock &BB : F) {
    for (Instruction &I : BB) {
      auto *store_inst = dyn_cast<StoreInst>(&I);
      if (!store_inst) continue;

      Value *dest = store_inst->getValueOperand();     // 저장되는 값
      Value *source = store_inst->getPointerOperand();  // 저장 위치

      // source(포인터 위치)가 global인지 확인: inttoptr(addr to Ty*) 형태
      auto *source_ce = dyn_cast<ConstantExpr>(source);
      if (!source_ce || source_ce->getOpcode() != Instruction::IntToPtr) continue;
      auto *source_ci = dyn_cast<ConstantInt>(source_ce->getOperand(0));
      if (!source_ci) continue;
      int64_t source_addr = source_ci->getSExtValue();
      if (!global_var_map_.count(source_addr)) continue;
      if (!addr_global_map_.count(source_addr)) continue;
      std::string source_gv_name = global_var_map_[source_addr];

      // dest(저장값)가 global 주소값(bare ConstantInt)인지 확인
      auto *dest_ci = dyn_cast<ConstantInt>(dest);
      if (!dest_ci) continue;
      int64_t dest_addr = dest_ci->getSExtValue();
      if (!global_var_map_.count(dest_addr)) continue;
      if (!addr_global_map_.count(dest_addr)) continue;
      std::string dest_gv_name = global_var_map_[dest_addr];

      // type_graph 상 실제로 source -> dest 포인터 관계인지 확인
      // (points_to_graph 단계에서 이미 이 관계로 edge를 만들었음)
      std::set<Node> succs = type_graph.getEdges(source_gv_name);
      bool is_real_ptr_edge =
          succs.find(Node{dest_gv_name, NodeType::Global}) != succs.end();
      if (!is_real_ptr_edge) continue;   // 관계 아니면 fallback(ReplaceUseOfGlobalVar)에 맡김

      GlobalVariable *source_gv = addr_global_map_[source_addr];
      GlobalVariable *dest_gv = addr_global_map_[dest_addr];

      // source_gv의 원소 타입(=source_gv가 담는 값의 타입)과 dest_gv 타입이
      // 다르면 bitcast, 같으면 그대로 저장
      Type *elem_ty = source_gv->getValueType(); // source_gv가 실제로 담는 타입
      Value *value_to_store = dest_gv;
      if (dest_gv->getType() != elem_ty) {
        value_to_store = ConstantExpr::getBitCast(dest_gv, elem_ty);
      }

      IRBuilder<> builder(store_inst);
      builder.CreateStore(value_to_store, source_gv);
      trash_can.push_back(store_inst);
    }
  }

  for (Instruction *i : trash_can)
    i->eraseFromParent();
}


// -------------------------
// ReplaceArrayBaseAliasVars
// -------------------------
// 배열 offset에 속한 var들은(정의하는 인스트럭션 종류와 무관하게) 전부
// "배열의 시작 주소(index 0)"를 나타낸다. 이 var들의 def를 통째로
// GEP(arr_alloca, 0, 0)로 교체한다. 인덱스가 있는 동적 접근은
// ReplaceUsesofArrayVar / ReplaceArrayVarinLoop가 이미 별도로 처리했으므로,
// 여기서는 그 로직이 손대지 않은(=아직 def가 살아있는) var들만 대상이 된다.
void VarRecover::ReplaceArrayBaseAliasVars(Function &F) {
  LLVMContext &ctx = F.getContext();
  Type *idx_ty = Type::getInt32Ty(ctx);

  for (auto &pair : array_info_map_) {
    const std::string &array_offset = pair.first;

    if (!offset_alloca_map_.count(array_offset)) continue;
    AllocaInst *arr_alloca = offset_alloca_map_[array_offset];

    if (!offset_vars_map_.count(array_offset)) continue;
    std::set<std::string> vars = offset_vars_map_[array_offset];

    std::vector<Instruction *> trash_can;

    for (const std::string &var : vars) {
      Instruction *def = GetDef(F, var);
      if (!def) continue;                 // 이미 다른 로직에서 지워졌으면 skip
      if (def->getNumUses() == 0) continue; // 아무도 안 쓰면 굳이 교체할 필요 없음

      IRBuilder<> builder(def);
      Value *gep = builder.CreateGEP(
          arr_alloca->getAllocatedType(), arr_alloca,
          {ConstantInt::get(idx_ty, 0), ConstantInt::get(idx_ty, 0)},
          "arr_base");

      Value *replacement = gep;
      if (def->getType() != gep->getType()) {
        if (def->getType()->isIntegerTy()) {
          // 원래 정수 값(esp-28 같은 add 결과, 혹은 load i32 결과)이었던 자리
          replacement = builder.CreatePtrToInt(gep, def->getType(), "arr_base_i");
        } else if (def->getType()->isPointerTy()) {
          // 원래 다른 포인터 타입(inttoptr to i32* 등)이었던 자리
          replacement = builder.CreateBitCast(gep, def->getType(), "arr_base_p");
        } else {
          llvm::report_fatal_error(
              "[ReplaceArrayBaseAliasVars] unexpected def type for array base alias");
        }
      }

      def->replaceAllUsesWith(replacement);
      trash_can.push_back(def);
    }

    for (Instruction *i : trash_can)
      i->eraseFromParent();
  }
}

// -------------------------
// ReplaceUsesOfVar
// -------------------------

void VarRecover::ReplaceUsesOfVar(Function &F, TypeGraph &type_graph) {
  std::vector<std::pair<Instruction*, AllocaInst*>> def_vec;
  std::vector<std::pair<Instruction*, Value*>> def_vec2;

  for (auto &pair : var_alloca_map_) {
    std::string var = pair.first;
    AllocaInst *alloca_inst = pair.second;

    if (!alloca_inst) continue;
    Instruction *def = GetDef(F, var);
    if (!def) continue;  
    if (!def->getType()->isPointerTy()) {
      continue;
    }

    if (alloca_inst->getAllocatedType()->isPointerTy()) {
      ReplaceUseofPointerVar(F, type_graph, var);
      continue;
    }

    if(alloca_inst->getAllocatedType()->isArrayTy()) {
      ReplaceUsesofArrayVar(F, var);
      continue;
    }

    // 타입이 다른 포인터: 그래프가 이미 결정한 bitcast만 반영
    if (def->getType() != alloca_inst->getType()) {
      std::string offset = var_offset_map_[var];
      std::set<Node> succs = type_graph.getEdges(offset);

      const Node *matched_bitcast = nullptr;
      for (const Node &succ : succs) {
        if (succ.getType() != NodeType::Bitcast) continue;
        Type *bitcast_ty = type_graph.getNodeType(succ.getName());
        if (bitcast_ty == def->getType()) {
          matched_bitcast = &succ;
          break;
        }
      }

      // 그래프에 근거 없는 타입 불일치는 손대지 않음
      if (!matched_bitcast) {
        outs() << "[ReplaceUsesOfVar] skip (no graph-confirmed bitcast) var: " << var << "\n";
        continue;
      }

      if (def->getNumUses() == 0) continue;

      Instruction *insert_point = alloca_inst->getNextNode();
      IRBuilder<> builder(insert_point);
      Value *bitcast_inst =
          builder.CreateBitCast(alloca_inst, def->getType(), "type_bitcast");

      def_vec2.push_back({def, bitcast_inst});
      continue;
    }


    def_vec.push_back({def, alloca_inst});
  }

  for (auto &p : def_vec) {
    p.first->replaceAllUsesWith(p.second);
  }
  for (auto &p : def_vec2) {
    p.first->replaceAllUsesWith(p.second);
  }
}

// -------------------------
// ReplaceUsesofArrayVar
// -------------------------

void VarRecover::ReplaceUsesofArrayVar(Function& F, std::string var) {
  Instruction* ptr_def = GetDef(F, var);

  // %1 = inttoptr %tmp to i32
  if(auto* inttoptr_inst = dyn_cast<IntToPtrInst>(ptr_def)) {
    Value* op = inttoptr_inst->getOperand(0);

    // %tmp = %esp - x
    std::string op_name = GetVarName(F, op);
    Instruction* esp_def = GetDef(F, op_name);
    
    if(auto* add_inst = dyn_cast<BinaryOperator>(esp_def)) {
      if(add_inst->getOpcode() == Instruction::Add) {
        Value* first_op = add_inst->getOperand(0);
        Value* arg_esp = F.getArg(0);

        if(first_op == arg_esp) {
          Value* offset = add_inst->getOperand(1);
          
          if(auto* const_int = dyn_cast<ConstantInt>(offset)) {
            int64_t const_offset = const_int->getSExtValue();
            
            ArrayInfo* arr_info = nullptr;
            for(auto& pair : array_info_map_) {
              ArrayInfo& info = pair.second;
              if(const_offset >= info.start && const_offset < info.end) {
                arr_info = &info;
                break;
              }
            }

            if(!arr_info) return;

            // index 계산
            int index = (const_offset - arr_info->start) / arr_info->element_size;

            // gep create
            LLVMContext& ctx = F.getContext();
            IRBuilder<> builder(inttoptr_inst);
            AllocaInst* arr_alloca = offset_alloca_map_[arr_info->offset];
            Type* elem_ty = TypeStrToLLVMType(ctx, arr_info->type);

            Value* gep = builder.CreateGEP(
              ArrayType::get(elem_ty, arr_info->size),
              arr_alloca,
              {ConstantInt::get(Type::getInt32Ty(ctx), 0),
              ConstantInt::get(Type::getInt32Ty(ctx), index)},
              "arr_gep"
            );

            inttoptr_inst->replaceAllUsesWith(gep);
          }
        }
      }
    }
  }
}


// -------------------------
// ReplaceArrayVar
// -------------------------

void VarRecover::ReplaceArrayVarinLoop(Function &F) {
  LLVMContext &ctx = F.getContext();

  for (auto &pair : array_info_map_) {
    // 배열 offset
    std::string offset = pair.first;
    // 배열 size 등 정보
    ArrayInfo info = pair.second;

    // alloca가 없으면 skip
    if (!offset_alloca_map_.count(offset)) continue;
    AllocaInst *alloca_inst = offset_alloca_map_[offset];

    // replace 할 offset과 매핑된 변수가 없으면 skip
    if (!offset_vars_map_.count(offset)) continue;
    std::set<std::string> vars = offset_vars_map_[offset];

    for (std::string var : vars) {
      // replace 할 변수의 def를 가져옴
      Instruction *def = GetDef(F, var);
      if (!def) continue;

      for (User *u : def->users()) {
        // add inst만 처리
        BinaryOperator *add_inst = dyn_cast<BinaryOperator>(u);
        if (!add_inst || add_inst->getOpcode() != Instruction::Add) continue;

        // something = add의 operand 중 def가 아닌 쪽
        Value *something = nullptr;
        if (add_inst->getOperand(0) == def)
          something = add_inst->getOperand(1);
        else if (add_inst->getOperand(1) == def)
          something = add_inst->getOperand(0);
        else
          continue;

        // index 추출
        Value *index = nullptr;

        if (BinaryOperator *bin_op = dyn_cast<BinaryOperator>(something)) {
          if (bin_op->getOpcode() == Instruction::Shl) {
            ConstantInt *shift = dyn_cast<ConstantInt>(bin_op->getOperand(1));
            if (shift && (1 << shift->getZExtValue()) == info.element_size)
              index = bin_op->getOperand(0);

          } else if (bin_op->getOpcode() == Instruction::Mul) {
            ConstantInt *mul_val = dyn_cast<ConstantInt>(bin_op->getOperand(1));
            if (!mul_val)
              mul_val = dyn_cast<ConstantInt>(bin_op->getOperand(0));

            if (mul_val && (int)mul_val->getZExtValue() == info.element_size) {
              if (mul_val == dyn_cast<ConstantInt>(bin_op->getOperand(1)))
                index = bin_op->getOperand(0);
              else
                index = bin_op->getOperand(1);
            }
          }
        }

        if (!index) continue;

        // add의 users 중 inttoptr 찾기
        for (User *u2 : add_inst->users()) {
          IntToPtrInst *itp = dyn_cast<IntToPtrInst>(u2);
          if (!itp) continue;

          std::vector<Instruction *> trash_can;

          for (User *u3 : itp->users()) {
            IRBuilder<> builder(cast<Instruction>(u3));

            Type *elem_ty = TypeStrToLLVMType(ctx, info.type);
            Value *gep = builder.CreateGEP(
                ArrayType::get(elem_ty, info.size),
                alloca_inst,
                {ConstantInt::get(Type::getInt32Ty(ctx), 0), index},
                "arr_gep");

            if (LoadInst *load = dyn_cast<LoadInst>(u3)) {
              Value *new_load = builder.CreateLoad(elem_ty, gep, "arr_load");
              load->replaceAllUsesWith(new_load);
              trash_can.push_back(load);
            } else if (StoreInst *store = dyn_cast<StoreInst>(u3)) {
              if (store->getPointerOperand() == itp) {
                builder.CreateStore(store->getValueOperand(), gep);
                trash_can.push_back(store);
              }
            }
          }

          for (Instruction *i : trash_can)
            i->eraseFromParent();
        }
      }
    }
  }
}


// -------------------------
// MakeVar / run
// -------------------------

void VarRecover::MakeVar(Function &F) {
  MakeAlloca(F);
}

void VarRecover::printSymexMap() {
  for(auto pair : offset_vars_map_) {
    outs() << "offset: " << pair.first << "\n";
    for(auto var : offset_vars_map_[pair.first]) {
      outs() << "var: " << var << "\n";
    }
  }
}

void VarRecover::run(Function &F) {
  SetSymexMap(F);
  SetStackLayoutMap();
  SetGlobalVarMap();
  MakeVar(F);
}

// -------------------------
// Getter들
// -------------------------

std::map<std::string, std::string> VarRecover::GetVarOffsetMap() {
  return var_offset_map_;
}
std::map<std::string, AllocaInst *> VarRecover::GetOffsetAllocaMap() {
  return offset_alloca_map_;
}

std::map<std::string, std::set<std::string>> VarRecover::GetOffsetMap() {
  return offset_vars_map_;
}
std::map<std::string, int> VarRecover::GetArrayIndexMap() {
  return array_index_map_;
}
