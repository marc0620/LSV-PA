#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <string>
#include <cmath>
#include "sat/cnf/cnf.h"
extern "C"{
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_sym_bdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_sym_sat(Abc_Frame_t* pAbc, int argc, char** argv);
static int Lsv_sym_all(Abc_Frame_t* pAbc, int argc, char** argv);
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_bdd", Lsv_sym_bdd, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_sat", Lsv_sym_sat, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sym_all", Lsv_sym_all, 0);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;


void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachNode(pNtk, pObj, i) {
    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
    Abc_Obj_t* pFanin;
    int j;
    Abc_ObjForEachFanin(pObj, pFanin, j) {
      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
             Abc_ObjName(pFanin));
    }
    if (Abc_NtkHasSop(pNtk)) {
      printf("The SOP of this node:\n%s", (char*)pObj->pData);
    }
  }
}

int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
        goto usage;
      default:
        goto usage;
    }
  }
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  Lsv_NtkPrintNodes(pNtk);
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
  Abc_Print(-2, "\t        prints the nodes in the network\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}

int Lsv_sym_all(Abc_Frame_t* pAbc, int argc, char** argv){
  if(argc<2 || argc>2){
    Abc_Print(-1, "Usage: lsv sym bdd <PO: k>\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(Abc_NtkIsStrash(pNtk)==NULL){
    Abc_Print(-1, "The network is not Aig logic.\n");
  }
  int i=0;
  Abc_Obj_t* pPi, *pPo, *pFanin, *pRoot;
  int count=0;
  int func=std::stoi(argv[1]);
  pPo = Abc_NtkPo(pNtk, func);
  pRoot=Abc_ObjFanin0(pPo);
  //Abc_Print(-2, "type pPo: %d, type root: %d\n", pPo->Type ,pRoot->Type);
  Abc_Ntk_t* pNewNtk = Abc_NtkCreateCone(pNtk, pRoot,Abc_ObjName(pPo), 1);
  Aig_Man_t* targetAig=Abc_NtkToDar(pNewNtk, 0, 0);
  
  Cnf_Dat_t* pCnf = Cnf_Derive(targetAig, 1);
  
  Cnf_Dat_t* pCnf2 = Cnf_Derive(targetAig, 1);
  
  sat_solver* pSat = sat_solver_new();
  
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
  
  Cnf_DataLift(pCnf2, pCnf->nVars);
 //Abc_Print(-2, "pCnf->nVars: %d %d\n", pCnf->nVars, pCnf2->nVars);
  
  Cnf_DataWriteIntoSolverInt(pSat, pCnf2, 1, 0);
  
  Aig_Obj_t* pVar;
  pVar=Aig_ManCo(targetAig, 0);
  lit lits[2];
 //Abc_Print(-2,"id: %d\n",pVar->Id);

 //Abc_Print(-2, "var num: %d\n", pCnf->pVarNums[pVar->Id]);
  lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
  lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 1);
  sat_solver_addclause(pSat, lits, lits+2);
  lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
  lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 0);
  sat_solver_addclause(pSat, lits, lits+2);
  int* ctrls=new int[Aig_ManCiNum(targetAig)];
  Aig_ManForEachCi(targetAig,pVar, i){
    ctrls[i]= sat_solver_addvar(pSat);
  }
  Aig_ManForEachCi(targetAig, pVar, i){
    lit lits[4];
   //Abc_Print(-2,"varnum: %d, i: %d ", pCnf->pVarNums[pVar->Id],i );
    int j=0;
    Aig_Obj_t* pVar1;
    Aig_ManForEachCi(targetAig,pVar1,j){
      if(i==j){
        lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
        lits[1]=toLitCond(pCnf2->pVarNums[pVar1->Id], 0);
        lits[2]=toLitCond(ctrls[i], 0);
        sat_solver_addclause(pSat, lits, lits+3);
        lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
        lits[1]=toLitCond(pCnf2->pVarNums[pVar1->Id], 1);
        lits[2]=toLitCond(ctrls[i], 0);
        sat_solver_addclause(pSat, lits, lits+3);
      }else{
        lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
        lits[1]=toLitCond(pCnf2->pVarNums[pVar1->Id], 0);
        lits[2]=toLitCond(ctrls[i], 1);
        lits[3]=toLitCond(ctrls[j], 1);
        sat_solver_addclause(pSat, lits, lits+4);
        lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
        lits[1]=toLitCond(pCnf2->pVarNums[pVar1->Id], 1);
        lits[2]=toLitCond(ctrls[i], 1);
        lits[3]=toLitCond(ctrls[j], 1);
        sat_solver_addclause(pSat, lits, lits+4);
      }
    }
  }
  lit* assumptions= new lit[Aig_ManCiNum(targetAig)]; 
    //initilize assumptions
    for(int i=0;i<Aig_ManCiNum(targetAig);i++){
      assumptions[i]=toLitCond(ctrls[i], 1);
    }
    for(int i=0;i<Aig_ManCiNum(targetAig);i++){
      assumptions[i]=toLitCond(ctrls[i], 0);
      for(int j=i+1;j<Aig_ManCiNum(targetAig);j++){
        assumptions[j]=toLitCond(ctrls[j], 0);
        if(sat_solver_solve(pSat, assumptions, assumptions+Aig_ManCiNum(targetAig), 0, 0, 0, 0)==-1){
          Abc_Print(-2,"%d %d\n", i, j);
        }
        assumptions[j]=toLitCond(ctrls[j], 1);
      }
      assumptions[i]=toLitCond(ctrls[i], 1);
    }

  return 0;


}
int Lsv_sym_sat(Abc_Frame_t* pAbc, int argc, char** argv){
  if(argc<4 || argc>4){
    Abc_Print(-1, "Usage: lsv sym bdd <PO: k> <PI1: i> <PI2: j>\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(Abc_NtkIsStrash(pNtk)==NULL){
    Abc_Print(-1, "The network is not Aig logic.\n");
  }
  char* targetNames[2];
  int i=0;
  Abc_Obj_t* pPi, *pPo, *pFanin, *pRoot;
  int count=0;
  int func=std::stoi(argv[1]);
  int tar1=std::stoi(argv[2]);
  int tar2=std::stoi(argv[3]);
  if(tar1>tar2){
    int temp=tar1;
    tar1=tar2;
    tar2=temp;
  }
  if(tar1==tar2){
    Abc_Print(-2, "symmetric\n");
    return 0;
  }
  pPo = Abc_NtkPo(pNtk, func);
  pRoot=Abc_ObjFanin0(pPo);
  //Abc_Print(-2, "type pPo: %d, type root: %d\n", pPo->Type ,pRoot->Type);
  Abc_NtkForEachPi(pNtk, pPi, i){
    if(i==tar1||i==tar2){
      targetNames[count]=Abc_ObjName(pPi);
     //Abc_Print(-2, "target PI: %s\n", targetNames[count]);
      count++;
    }
  }
  Abc_Ntk_t* pNewNtk = Abc_NtkCreateCone(pNtk, pRoot,Abc_ObjName(pPo), 1);
  Aig_Man_t* targetAig=Abc_NtkToDar(pNewNtk, 0, 0);
  
  Cnf_Dat_t* pCnf = Cnf_Derive(targetAig, 1);
  
  Cnf_Dat_t* pCnf2 = Cnf_Derive(targetAig, 1);
  
  sat_solver* pSat = sat_solver_new();
  
  Cnf_DataWriteIntoSolverInt(pSat, pCnf, 1, 0);
  
  Cnf_DataLift(pCnf2, pCnf->nVars);
 //Abc_Print(-2, "pCnf->nVars: %d %d\n", pCnf->nVars, pCnf2->nVars);
  
  Cnf_DataWriteIntoSolverInt(pSat, pCnf2, 1, 0);
  
  Aig_Obj_t* pVar;
  pVar=Aig_ManCo(targetAig, 0);
  lit lits[2];
 //Abc_Print(-2,"id: %d\n",pVar->Id);

 //Abc_Print(-2, "var num: %d\n", pCnf->pVarNums[pVar->Id]);
  lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
  lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 1);
  sat_solver_addclause(pSat, lits, lits+2);
  lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
  lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 0);
  sat_solver_addclause(pSat, lits, lits+2);
  Aig_ManForEachCi(targetAig, pVar, i){
    lit lits[2];
   //Abc_Print(-2,"varnum: %d, i: %d ", pCnf->pVarNums[pVar->Id],i );
    if(i==tar1||i==tar2){
      lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
      lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 1);
      sat_solver_addclause(pSat, lits, lits+2);
      lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
      lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 0);
      sat_solver_addclause(pSat, lits, lits+2);
    }else{
      lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 1);
      lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 0);
      sat_solver_addclause(pSat, lits, lits+2);
      lits[0]=toLitCond(pCnf->pVarNums[pVar->Id], 0);
      lits[1]=toLitCond(pCnf2->pVarNums[pVar->Id], 1);
      sat_solver_addclause(pSat, lits, lits+2);
    }
  }
  Aig_Obj_t* targetVar1=Aig_ManCi(targetAig, tar1);
  Aig_Obj_t* targetVar2=Aig_ManCi(targetAig, tar2);
  lits[0]=toLitCond(pCnf->pVarNums[targetVar1->Id], 1);
  lits[1]=toLitCond(pCnf->pVarNums[targetVar2->Id], 1);
  sat_solver_addclause(pSat, lits, lits+2);
  lits[0]=toLitCond(pCnf->pVarNums[targetVar1->Id], 0);
  lits[1]=toLitCond(pCnf->pVarNums[targetVar2->Id], 0);
  sat_solver_addclause(pSat, lits, lits+2);
  lits[0]=toLitCond(pCnf2->pVarNums[targetVar1->Id], 1);
  lits[1]=toLitCond(pCnf2->pVarNums[targetVar2->Id], 1);
  sat_solver_addclause(pSat, lits, lits+2);
  lits[0]=toLitCond(pCnf2->pVarNums[targetVar1->Id], 0);
  lits[1]=toLitCond(pCnf2->pVarNums[targetVar2->Id], 0);
  sat_solver_addclause(pSat, lits, lits+2);
  int result=sat_solver_solve(pSat, NULL, NULL, 0, 0, 0, 0);
  if(result==-1){
    Abc_Print(-2, "symmetric\n", 0);
  }else if(result==1){
    Abc_Print(-2, "asymmetric\n", 0);
    Aig_ManForEachCi(targetAig, pVar, i){
        Abc_Print(-2, "%d", sat_solver_var_value(pSat, pCnf->pVarNums[pVar->Id]));
    }
    Abc_Print(-2, "\n", 0);
    Aig_ManForEachCi(targetAig, pVar, i){
      Abc_Print(-2, "%d", sat_solver_var_value(pSat, pCnf2->pVarNums[pVar->Id]));
    }
    Abc_Print(-2, "\n", 0);
  }else{
   //Abc_Print(-2, "unknown\n", 0);
  }

  return 0;

}
int printCase(char* values,int* sup, int posNum, int num, int tar1, int tar2){
 //Abc_Print(-2, "posNum: %d, num: %d, tar1: %d, tar2: %d\n", posNum, num,tar1, tar2);
  for(int i=0;i<num;i++){
    //Abc_Print(-2, "%d ", sup[i]);
    if (i==tar1){
      Abc_Print(-2, "%d", 0);
    } else if(i==tar2){
      Abc_Print(-2, "%d", 1);
    } else{
      if(sup[i]!=-1){
        Abc_Print(-2, "%d", ((int)values[sup[i]])%2);
      } else {
        Abc_Print(-2, "%d", 0);
      }
    }
  }
  Abc_Print(-2, "\n", 0);
  for(int i=0;i<num;i++){
    //Abc_Print(-2, "%d ", sup[i]);
    if (i==tar1){
      Abc_Print(-2, "%d", 1);
    } else if(i==tar2){
      Abc_Print(-2, "%d", 0);
    } else{
      if(sup[i]!=-1){
        Abc_Print(-2, "%d", ((int)values[sup[i]])%2);
      } else {
        Abc_Print(-2, "%d", 0);
      }
    }
  }
  Abc_Print(-2, "\n", 0);
  return 0;
}

int Lsv_sym_bdd(Abc_Frame_t* pAbc, int argc, char** argv){
  if(argc<4 || argc>4){
    Abc_Print(-1, "Usage: lsv sym bdd <PO: k> <PI1: i> <PI2: j>\n");
    return 1;
  }
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(Abc_NtkIsBddLogic(pNtk)==NULL){
    Abc_Print(-1, "The network is not BDD logic.\n");
  }
  char* targetNames[2];
  int i=0;
  Abc_Obj_t* pPi, *pPo, *pRoot, *pFanin;
  int count=0;
  int func=std::stoi(argv[1]);
  int tar1=std::stoi(argv[2]);
  int tar2=std::stoi(argv[3]);
  if(tar1==tar2){
    Abc_Print(-2, "symmetric\n");
    return 0;
  }
  if(tar1>tar2){
    int temp=tar1;
    tar1=tar2;
    tar2=temp;
  }
  Abc_NtkForEachPi(pNtk, pPi, i){
    if(i==tar1||i==tar2){
      targetNames[count]=Abc_ObjName(pPi);
     //Abc_Print(-2, "target PI: %s\n", targetNames[count]);
      count++;
    }
  }
  DdManager* dd = (DdManager*)pNtk->pManFunc;
 //Abc_Print(-2, "ntk pi num: %d\n", Abc_NtkPiNum(pNtk));
  pPo = Abc_NtkPo(pNtk, func);
  pRoot=Abc_ObjFanin0(pPo);
  DdNode* bdd = (DdNode*)pRoot->pData;
  //int* ddsup=Cudd_SupportIndex(dd, bdd);
  //for(int i=0;i<(dd->size);i++){
  //  Abc_Print(-2, "%d ", ddsup[i]);
  //}
  DdNode* bdd01, *bdd10;
  count=0;
 //Abc_Print(-2, "fanin num: %d\n", Abc_ObjFaninNum(pRoot));
  bdd01=bdd;
  bdd10=bdd;
  int* sup=new int[Abc_NtkPiNum(pNtk)];
  for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
    sup[i]=-1;
  }
  Abc_ObjForEachFanin( pRoot, pFanin, i ){
    char* name=Abc_ObjName(pFanin);
   //Abc_Print(-2, "fanin name: %s\n", name);
    int j=0;
    Abc_NtkForEachPi(pNtk, pPi, j){
     //Abc_Print(-2, "PI: %s\n", Abc_ObjName(pPi));
      if(strcmp(name, Abc_ObjName(pPi))==0){
        sup[j]=i;
        //Abc_Print(-2, "Pi: %d in sup\n", j);
        break;
      }
    }
    if(strcmp(name, targetNames[0])==0 || strcmp(name, targetNames[1])==0){
        bdd01=Cudd_Cofactor(dd, bdd01, Cudd_NotCond(Cudd_bddIthVar(dd, i),count==0));
        Cudd_Ref(bdd01);
        bdd10=Cudd_Cofactor(dd, bdd10, Cudd_NotCond(Cudd_bddIthVar(dd, i),count==1));
        Cudd_Ref(bdd10);
        count++;
    }
  }
  //for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
  //  Abc_Print(-2, "%d ", sup[i]);
  //}
 //Abc_Print(-2, "bdd support size: %d\n", Cudd_SupportSize(dd, bdd));
 //Abc_Print(-2, "count: %d\n", count);
  if(count==0){
    Abc_Print(-2, "symmetric\n");
    return 0;
  }
  // now we have 2 symmatric comparison bdd
  // we need to compare them
  DdNode* miter=Cudd_bddXor(dd, bdd01, bdd10);
  Cudd_Ref(miter);
  //Abc_Print(-2,"miter supportsize: %d, bdd01 supportsize: %d, bdd10 supportsize: %d, bdd support size: %d\n",Cudd_SupportSize(dd, miter),Cudd_SupportSize(dd, bdd01),Cudd_SupportSize(dd, bdd10),Cudd_SupportSize(dd, bdd));
  char* cube = new char[Abc_NtkPiNum(pNtk)+1];
  for(int i=0;i<Abc_NtkPiNum(pNtk)+1;i++){
    cube[i]=-1;
  }

  if(Cudd_bddPickOneCube(dd, miter, cube)==0){
    Abc_Print(-2, "symmetric\n", 0);
    return 0;
  }else{
    Abc_Print(-2, "asymmetric\n", 0);
    //for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
    //  Abc_Print(-2, "%d ", (int)cube[i]);
    //}
    printCase(cube, sup,Cudd_SupportSize(dd, bdd01), Abc_NtkPiNum(pNtk), tar1, tar2);
  }
  Cudd_RecursiveDeref(dd, bdd01);
  Cudd_RecursiveDeref(dd, bdd10);
  Cudd_RecursiveDeref(dd, miter);
  return 0;
}