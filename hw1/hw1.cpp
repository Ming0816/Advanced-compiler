#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"
#include "llvm/IR/Constants.h"
#include <stdio.h>
#include <math.h>

using namespace std;
using namespace llvm;

namespace {
struct IRArray {
  const char *arrayName;
  int add;
  int sub;
  int mul;
  int read = 0;
  int write = 0;
  int order;
};
vector<IRArray> Arr[2]; // index 0 for read array references; index 1 for write array references
int High = 0, Low = 0;

/*
The solution vector is represented as,

    X= X0 + XCoeffT *t;
    y= Y0 + YCoeffT *t;

*/
struct SolEquStru {
  int   is_there_solution;
  int   X0;
  int   XCoeffT;
  int   Y0;
  int   YCoeffT;
}  ;

/*  
The TriStru is used to hold the gcd information.
  Let gcd = GCD(a,b)  ===> a*x+b*y = gcd
*/ 
struct TriStru{
  int   gcd;
  int   x;
  int   y;
} ;


/*  

The main subroutine, given a, b,
return x, y, g, where a*x+b*y =g;

*/
struct TriStru Extended_Euclid(int a , int b)
{
  struct TriStru Tri1,Tri2;
  if (b==0) {
    Tri1.gcd=a;
    Tri1.x=1;
    Tri1.y=0;
    return Tri1;
    }
  Tri2=Extended_Euclid( b , (a%b));
  Tri1.gcd=Tri2.gcd;
  Tri1.x=Tri2.y;
  Tri1.y=Tri2.x-(a/b)*Tri2.y;
  return Tri1;
}

/*
  Solve the diophatine equation by given a,b, and c, where
    a*x+b*y =c

  return

    X= X0 + XCoeffT *t;
    y= Y0 + YCoeffT *t;

*/   
struct SolEquStru diophatine_solver(int a, int b, int c)
{
  int   k;
  struct TriStru   Triple;
  struct SolEquStru s;

   Triple=Extended_Euclid( a , b );
//   printf("a,b,g, x,y= %d %d %d %d %d \n",a,b,Triple.gcd,Triple.x,Triple.y);
   if ((c%Triple.gcd)==0) {
	    k=c/Triple.gcd;
	    s.X0=Triple.x*k;
	    s.XCoeffT=(b/Triple.gcd );
	    s.Y0=Triple.y*k;
	    s.YCoeffT=((-a)/Triple.gcd );
      s.is_there_solution=1;
   } else {
      s.is_there_solution=0;
   }

  return(s);
}  

int Min(int a, int b)
{
 if (a<=b) {return a;}
 else {return b;}
}

int Max(int a, int b)
{
 if (a>=b) {return a;}
 else {return b;}
}

void swap(int *a, int *b)
{
  int temp;
  temp = *a;
  *a = *b;
  *b = temp;
}

struct HW1Pass : public PassInfoMixin<HW1Pass> {
  PreservedAnalyses run(Function &F, FunctionAnalysisManager &FAM);
};

PreservedAnalyses HW1Pass::run(Function &F, FunctionAnalysisManager &FAM) {
  const char *name;
  int numStmt = 1;
  struct IRArray *getEle;
  // errs() << "[HW1]: " << F.getName() << '\n';

  for (BasicBlock &BB : F) {
  //  errs() << BB.getName() << '\n';

    if (!BB.getName().find("entry", 0)) {
      for (Instruction &I : BB) {
      //  errs() << I << '\n';

        if (auto *SI = dyn_cast<StoreInst>(&I)) {
          if (ConstantInt *Integer = dyn_cast<ConstantInt>(SI->getOperand(0))) {
            if (!strcmp("i", SI->getOperand(1)->getName().data())) {
              Low = Integer->getZExtValue();
            //  errs() << "Low : " << Low << '\n';
            }
          }
        }
      }
    } else if (!BB.getName().find("for.cond", 0)) {
      for (Instruction &I : BB) {
      //  errs() << I << '\n';
        if (!strcmp("icmp", I.getOpcodeName())) {
          if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(1))) {
            High = Integer->getZExtValue();
          //  errs() << "High : " << High << '\n';
          }
        }
      }
    } else if (!BB.getName().find("for.body", 0)) {
      for (Instruction &I : BB) {
      //  errs() << I << '\n';
        if (auto *LI = dyn_cast<LoadInst>(&I)) {
          if (!LI->getOperand(0)->getName().find("arrayidx", 0)) {
            getEle->read = 1;
            getEle->order = numStmt;
          //  errs() << "\nStatement S" << getEle->stmt <<
          //  ", Array name: " << getEle->arrayName << 
          //  ", Add = " << getEle->add <<
          //  ", Sub = " << getEle->sub << 
          //  ", Mul = " << getEle->mul <<
          //  ", Read = " << getEle->read << 
          //  ", Write = " << getEle->write << "\n\n";
            Arr[0].push_back(*getEle);

          } else if (!strcmp("i", LI->getOperand(0)->getName().data())) {
            struct IRArray newEle;
            getEle = &newEle;
            getEle->add = 0;
            getEle->sub = 0;
            getEle->mul = 1;
          }

        } else if (auto *SI = dyn_cast<StoreInst>(&I)) {
          if (!SI->getOperand(1)->getName().find("arrayidx", 0)) {
            getEle->write = 1;
            getEle->order = numStmt;
            numStmt++;
          //  errs() << "\nStatement S" << getEle->stmt <<
          //  ", Array name: " << getEle->arrayName << 
          //  ", Add = " << getEle->add <<
          //  ", Sub = " << getEle->sub << 
          //  ", Mul = " << getEle->mul <<
          //  ", Read = " << getEle->read << 
          //  ", Write = " << getEle->write << "\n\n";
            Arr[1].push_back(*getEle);
          }
        } else if (I.getOpcode() == Instruction::GetElementPtr) {
          name = I.getOperand(0)->getName().data();
          getEle->arrayName = name;
        } else if (I.getOpcode() == Instruction::Add) {
          if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(0))) {
            int add = Integer->getZExtValue();
            getEle->add += add;
          } else if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(1))) {
            int add = Integer->getZExtValue();
            getEle->add += add;
          }
        } else if (I.getOpcode() == Instruction::Sub) {
          if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(0))) {
            int sub = Integer->getZExtValue();
            getEle->sub -= sub;
          } else if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(1))) {
            int sub = Integer->getZExtValue();
            getEle->sub -= sub;
          }
        } else if (I.getOpcode() == Instruction::Mul) {
          if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(0))) {
            int mul = Integer->getZExtValue();
            getEle->mul *= mul;
          } else if (ConstantInt *Integer = dyn_cast<ConstantInt>(I.getOperand(1))) {
            int mul = Integer->getZExtValue();
            getEle->mul *= mul;
          }
        }
      }
    }
  }

  int a, b, c;
  int x_l, x_h, y_l, y_h;
  int lb, ub;
  int t1, t2;
  errs() << "====Flow Dependency====\n";
  for (int i = 0; i < Arr[1].size(); i++) { // Write vector
    for (int j = 0; j < Arr[0].size(); j++) { // Read vector
      x_l = y_l = Low;
      x_h = y_h = High - 1;
      if (!strcmp(Arr[1][i].arrayName, Arr[0][j].arrayName)) {
        a = Arr[1][i].mul;
        b = -Arr[0][j].mul;
        c = (Arr[0][j].add + Arr[0][j].sub) - (Arr[1][i].add + Arr[1][i].sub);
      
        
        struct SolEquStru f;
        f = diophatine_solver(a,b,c);
        /*
        if (f.is_there_solution) {
          printf("The solution of the diophatine equation %d x + %d y = % d\n",a,b,c);
          printf("X= %d + %d *t\n", f.X0,f.XCoeffT);
          printf("Y= %d + %d *t\n\n", f.Y0,f.YCoeffT);
        }
        else {
          printf("There is no solution for the diophatine equation %d x + %d y = % d\n",a,b,c);
        }
        */
        x_h -= f.X0;
        x_l -= f.X0;
        y_h -= f.Y0;
        y_l -= f.Y0;

        x_h /= f.XCoeffT;
        x_l /= f.XCoeffT;
        if (f.XCoeffT < 0)
          swap(&x_l, &x_h);
      
        y_h /= f.YCoeffT;
        y_l /= f.YCoeffT;
        if (f.YCoeffT < 0)
          swap(&y_l, &y_h);

        lb = Max(x_l, y_l);
        ub = Min(x_h, y_h);

        for (int k = lb; k <= ub; k++) {
          t1 = (f.X0 + (k*f.XCoeffT));
          t2 = (f.Y0 + (k*f.YCoeffT));
          if (t1 < t2 || (t1 == t2 && Arr[0][j].order > Arr[1][i].order)) {
            errs() << Arr[1][i].arrayName << ":S" << Arr[1][i].order << " -----> S" << Arr[0][j].order << '\n';
            errs() << "(i=" << t1 << ",i=" << t2 << ")\n";
          }
        }
      }
    }
  }

  errs() << "====Anti-Dependency====\n";
  for (int i = 0; i < Arr[0].size(); i++) { // Read vector
    for (int j = 0; j < Arr[1].size(); j++) { // Write vector
      x_l = y_l = Low;
      x_h = y_h = High - 1;
    
      if (!strcmp(Arr[0][i].arrayName, Arr[1][j].arrayName)) {
        a = Arr[0][i].mul;
        b = -Arr[1][j].mul;
        c = (Arr[1][j].add + Arr[1][j].sub) - (Arr[0][i].add + Arr[0][i].sub);
      
        struct SolEquStru f;
        f = diophatine_solver(a,b,c);
        /*
        if (f.is_there_solution) {
          printf("The solution of the diophatine equation %d x + %d y = % d\n",a,b,c);
          printf("X= %d + %d *t\n", f.X0,f.XCoeffT);
          printf("Y= %d + %d *t\n\n", f.Y0,f.YCoeffT);
        }
        else {
          printf("There is no solution for the diophatine equation %d x + %d y = % d\n",a,b,c);
        }
        */
        x_h -= f.X0;
        x_l -= f.X0;
        y_h -= f.Y0;
        y_l -= f.Y0;

        x_h /= f.XCoeffT;
        x_l /= f.XCoeffT;
        if (f.XCoeffT < 0)
          swap(&x_l, &x_h);
  
        y_h /= f.YCoeffT;
        y_l /= f.YCoeffT;
        if (f.YCoeffT < 0)
          swap(&y_l, &y_h);

        lb = Max(x_l, y_l);
        ub = Min(x_h, y_h);

        for (int k = lb; k <= ub; k++) {
          t1 = (f.X0 + (k*f.XCoeffT));
          t2 = (f.Y0 + (k*f.YCoeffT));
          if (t1 < t2 || (t1 == t2 && Arr[0][i].order < Arr[1][j].order)) {
            errs() << Arr[0][i].arrayName << ":S" << Arr[0][i].order << " --A--> S" << Arr[1][j].order << '\n';
            errs() << "(i=" << t1 << ",i=" << t2 << ")\n";
          }
        }
      }
    }
  }

  errs() << "====Output Dependency====\n";
  for (int i = 0; i < Arr[1].size(); i++) { // Write vector
    for (int j = 0; j < Arr[1].size(); j++) { // Write vector
      x_l = y_l = Low;
      x_h = y_h = High - 1;
      if (!strcmp(Arr[1][i].arrayName, Arr[1][j].arrayName)) {
        a = Arr[1][i].mul;
        b = -Arr[1][j].mul;
        c = (Arr[1][j].add + Arr[1][j].sub) - (Arr[1][i].add + Arr[1][i].sub);
      
        struct SolEquStru f;
        f = diophatine_solver(a,b,c);
        /*
        if (f.is_there_solution) {
          printf("The solution of the diophatine equation %d x + %d y = % d\n",a,b,c);
          printf("X= %d + %d *t\n", f.X0,f.XCoeffT);
          printf("Y= %d + %d *t\n\n", f.Y0,f.YCoeffT);
        }
        else {
          printf("There is no solution for the diophatine equation %d x + %d y = % d\n",a,b,c);
        }
        */
        x_h -= f.X0;
        x_l -= f.X0;
        y_h -= f.Y0;
        y_l -= f.Y0;

        x_h /= f.XCoeffT;
        x_l /= f.XCoeffT;
        if (f.XCoeffT < 0)
          swap(&x_l, &x_h);
      
        y_h /= f.YCoeffT;
        y_l /= f.YCoeffT;
        if (f.YCoeffT < 0)
          swap(&y_l, &y_h);

        lb = Max(x_l, y_l);
        ub = Min(x_h, y_h);

        for (int k = lb; k <= ub; k++) {
	        t1 = (f.X0 + (k*f.XCoeffT));
          t2 = (f.Y0 + (k*f.YCoeffT));
	        if (t1 < t2 || (t1 == t2 && Arr[1][j].order < Arr[1][i].order)) {	
          	errs() << Arr[1][i].arrayName << ":S" << Arr[1][i].order << " --O--> S" << Arr[1][j].order << '\n';
          	errs() << "(i=" << t1 << ",i=" << t2 << ")\n";
	        }
	      }
      }
    }
  }

  return PreservedAnalyses::all();
}

} // end anonymous namespace

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo() {
  return {LLVM_PLUGIN_API_VERSION, "HW1Pass", LLVM_VERSION_STRING,
          [](PassBuilder &PB) {
            PB.registerPipelineParsingCallback(
                [](StringRef Name, FunctionPassManager &FPM,
                   ArrayRef<PassBuilder::PipelineElement>) {
                  if (Name == "hw1") {
                    FPM.addPass(HW1Pass());
                    return true;
                  }
                  return false;
                });
          }};
}
