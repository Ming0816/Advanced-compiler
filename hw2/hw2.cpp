#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/InstIterator.h"
#include <llvm/IR/Instructions.h>
#include <llvm/Analysis/LoopInfo.h>
#include "llvm/Analysis/DependenceAnalysis.h"
#include <typeinfo>
#include <vector>
#include <set>
#include <string>

using namespace llvm;
using namespace std;

namespace {
vector<pair<string, string> > tdef;
vector<pair<string, string> > tequiv;
vector<pair<string, string> > tmp;
vector<pair<string, string> > tmp1;
vector<pair<string, string> > ::iterator it;
vector<pair<string, string> > ::iterator it2;
vector<string> tgen;
vector<string> tref;
vector<string> ::iterator it1;
int line_num = 1;
int size;
string ref_name;

void compute_TREF(Instruction &I) {
  if (auto *LI = dyn_cast<LoadInst>(&I)) {
    string name;
    string str = "";
    name = LI->getOperand(0)->getName().data();
    Value *val = LI->getOperand(0);
    if (val->hasName()) {
      ref_name = name;
      tref.push_back(ref_name);
    } else {
      ref_name = "*" + ref_name;
      name = ref_name;
      tref.push_back(name);
    }

    if (tequiv.size() > 0) {
      set<string> s(tref.begin(), tref.end());
      tref.clear();
      int size;
      do {
        size = s.size();
        for (int i = 0; i < tequiv.size(); i++) {
          if (!strcmp(name.c_str(), tequiv[i].first.c_str())) {
            str = tequiv[i].second;
            s.insert(str);
          } else if (!strcmp(name.c_str(), tequiv[i].second.c_str())) {
            str = tequiv[i].first;
            s.insert(str);
          }
        }
        name = str;
      } while (size < s.size());
      tref.insert(tref.begin(), s.begin(), s.end());
    }
  }
}

void compute_TGEN(Instruction &I) {
  if (auto *SI = dyn_cast<StoreInst>(&I)) {
    string name;
    string str = "";
    string num = "";
    name = SI->getOperand(1)->getName().data();
    Value *val = SI->getOperand(1);
    if (val->hasName()) {
      tgen.push_back(name);
    } else {
      ref_name = '*' + ref_name;
      name = ref_name;
      tgen.push_back(name);
    }
    num += 'S';
    num += to_string(line_num);
    tmp.push_back(make_pair(name, num));

    if (tequiv.size() > 0) {
      for (it = tequiv.begin(); it != tequiv.end(); ++it) {
        if (!strcmp(name.c_str(), (*it).first.c_str())) {
          str += (*it).second;
          tgen.push_back(str);
          tmp.push_back(make_pair(str, num));
          break;
        } else if (!strcmp(name.c_str(), (*it).second.c_str())) {
          str += (*it).first;
          tgen.push_back(str);
          tmp.push_back(make_pair(str, num));
          break;
        }
      }
    }

    for (int i = 0; i < tgen.size(); i++) {
      for (int j = 0; j < tequiv.size(); j++) {
        if (tequiv[j].first.find(tgen[i], 1) < 10) {
          tequiv.erase(tequiv.begin()+j);
        }
      }
    }
  }
}

void compute_DEP() {
  int flag = 0;
  errs() << "DEP:{";
  for (it = tdef.begin(); it != tdef.end(); ++it) {
    for (it1 = tref.begin(); it1 != tref.end(); ++it1) {
      if (!strcmp((*it).first.c_str(), (*it1).c_str())) {
        flag = 1;
        errs() << "\n    " << (*it).first << ": " << (*it).second << "--->" << "S" << line_num;
      }
    }
  }

  for (it = tdef.begin(); it != tdef.end(); ++it) {
    for (it1 = tgen.begin(); it1 != tgen.end(); ++it1) {
      if (!strcmp((*it).first.c_str(), (*it1).c_str())) {
        flag = 1;
        errs() << "\n    " << (*it).first << ": " << (*it).second << "-O->" << "S" << line_num;
      }
    }
  }
  if (!flag) {
    errs() << "}\n";
  } else {
    errs() << "\n}\n";
  }
}

void update_TDEF() {
  for (int i = 0; i < tgen.size(); i++) {
    for (int j = 0; j < tdef.size(); j++) {
      if (!strcmp(tgen[i].c_str(), tdef[j].first.c_str())) {
        tdef.erase(tdef.begin()+j);
      }
    }
  }
  tdef.insert(tdef.end(), tmp.begin(), tmp.end());
  tmp.clear();
}

void update_TEQUIV(Instruction &I) {
  string alias1, alias2;
  string name = I.getOperand(1)->getName().data();
  Type *opType = I.getOperand(0)->getType();
  string typeStr;
  raw_string_ostream typeStream(typeStr);
  opType->print(typeStream);
  typeStream.flush();

  Value *val = I.getOperand(1);
  if (!val->hasName()) {
    name = ref_name;
  }

  if (!strcmp("ptr", typeStr.c_str())) {
    name = "*" + name;
    tequiv.push_back(make_pair(name, I.getOperand(0)->getName().data()));
  }

  for (it = tequiv.begin(); it != tequiv.end(); ++it) {
    alias1 = '*' + (*it).first;
    alias2 = '*' + (*it).second;
    for (it2 = tequiv.begin(); it2 != tequiv.end(); ++it2) {
      if (it != it2) {
        if (!strcmp(alias1.c_str(), (*it2).first.c_str())) {
          name = alias2;
          tmp1.push_back(make_pair(name, (*it2).second));
        } else if (!strcmp(alias1.c_str(), (*it2).second.c_str())) {
          name = alias2;
          tmp1.push_back(make_pair(name, (*it2).first));
        } else if (!strcmp(alias2.c_str(), (*it2).first.c_str())) {
          name = alias1;
          tmp1.push_back(make_pair(name, (*it2).second));
        } else if (!strcmp(alias2.c_str(), (*it2).second.c_str())) {
          name = alias1;
          tmp1.push_back(make_pair(name, (*it2).first));
        }
      }
    }
  }
  tequiv.insert(tequiv.end(), tmp1.begin(), tmp1.end());
  tmp1.clear();
}

void print_TREF() {
  errs() << "TREF: {";
  for (it1 = tref.begin(); it1 != tref.end(); ++it1) {
    if (it1 == tref.end()-1) {
      errs() << *it1;
    } else {
      errs() << *it1 << ", ";
    }
  }
  errs() << "}\n";
}

void print_TGEN() {
  errs() << "TGEN: {";
  for (it1 = tgen.begin(); it1 != tgen.end(); ++it1) {
    if (it1 == tgen.end()-1) {
      errs() << *it1;
    } else {
      errs() << *it1 << ", ";
    }
  }
  errs() << "}\n";
}

void print_TDEF() {
  errs() << "TDEF:{";
  for (it = tdef.begin(); it != tdef.end(); ++it) {
    errs() << "(" << (*it).first << ", " << (*it).second << ")";
    if (it != tdef.end()-1) {
      errs() << ", ";
    }
  }
  errs() << "}\n";
}

void print_TEQUIV() {
  set<pair<string, string> > s(tequiv.begin(), tequiv.end());
  set<pair<string, string> > ::iterator it;
  int size = s.size()-1;
  int i = 0;
  
  errs() << "TEQUIV:{";
  for (it = s.begin(); it != s.end(); ++it, i++) {
    errs() << "(" << (*it).first << ", " << (*it).second << ")";
    if (i < size) {
      errs() << ", ";
    }
  }
  errs() << "}\n\n";
}

struct HW2Pass : public PassInfoMixin<HW2Pass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

PreservedAnalyses HW2Pass::run(Function &F, FunctionAnalysisManager &FAM) {
  for (BasicBlock &BB : F) {
  //  errs() << BB.getName() << '\n';
    for (Instruction &I : BB) {
    //  errs() << I << '\n';
      compute_TREF(I);
      compute_TGEN(I);
      if (auto *SI = dyn_cast<StoreInst>(&I)) {
        errs() << "S" << line_num << ":--------------------\n";
        print_TREF();
        print_TGEN();
        compute_DEP();
        update_TDEF();
        print_TDEF();
        update_TEQUIV(I);
        print_TEQUIV();
        tref.clear();
        tgen.clear();
        line_num++;
      }
    }
  }

  return PreservedAnalyses::all();
}
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "HW2Pass", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "hw2") {
                    FPM.addPass(HW2Pass());
                    return true;
                  }
                  return false;
                });
          }};
}