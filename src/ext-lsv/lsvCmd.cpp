#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <string>
#include <cmath>
#include "sat/cnf/cnf.h"
#include "bdd/extrab/extraBdd.h"
#include <list>
//#include "base/abci/b"
extern "C"{
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int XDC_simp(Abc_Frame_t* pAbc, int argc, char** argv);
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "x", XDC_simp, 1);
}

void destroy(Abc_Frame_t* pAbc) {}

Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

typedef struct coneobj 
{
  int out_count=0;
  Abc_Obj_t * node=NULL;
}coneobj_t;



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

bool forallfanout(coneobj_t* node, bool* set){
  Abc_Obj_t* pFanout;
  int i;
  if(node->out_count!=0){
    //Abc_Print(-2, "node:%d out_count=%d\n", Abc_ObjId(node->node),node->out_count);
    return false;
  }
  Abc_ObjForEachFanout(node->node, pFanout, i){
    if(!set[Abc_ObjId(pFanout)]){
      node->out_count+=1;
    }
  }
  if(node->out_count>0)
    return false;
  else
    return true;
}
int recursive_include(coneobj_t* cone,int node, bool* set,bool* input){

  int total=1;
  int i;
  Abc_Obj_t* pFanin;
  if(input[node])
    input[node]=false;
  Abc_ObjForEachFanin(cone[node].node, pFanin, i){
    if(cone[Abc_ObjId(pFanin)].out_count==0)
      continue;
    else{
      if(--cone[Abc_ObjId(pFanin)].out_count==0){
        set[Abc_ObjId(pFanin)]=true;
        //Abc_Print(-2, "node %d set in recursive\n", Abc_ObjId(pFanin));
        total+=recursive_include(cone,Abc_ObjId(pFanin), set,input);
      }
      if(cone[Abc_ObjId(pFanin)].out_count<0){
        Abc_Print(-1, "out_count=%d\n", cone[Abc_ObjId(pFanin)].out_count);
      }
    }
  }
  return total;

}
int zerofanout(coneobj_t* cone,int node, bool* set, bool* input,int length){
  Abc_Obj_t* pFanin;
  int i;
  int total=0;
  Abc_ObjForEachFanin(cone[node].node, pFanin, i){
    if(Abc_ObjFanoutNum(pFanin)==1 || forallfanout(&cone[Abc_ObjId(pFanin)], set)){
      set[Abc_ObjId(pFanin)]=true;
      //Abc_Print(-2, "node %d set in zerofanout\n", Abc_ObjId(pFanin));
      total+=recursive_include(cone,Abc_ObjId(pFanin), set, input);
      total+=zerofanout(cone,Abc_ObjId(pFanin), set, input, length);
    }else{
      input[Abc_ObjId(pFanin)]=true;
    }
  }
  return total;
}

int XDC_simp(Abc_Frame_t* pAbc, int argc, char** argv){
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(Abc_NtkIsStrash(pNtk)==NULL){
    Abc_Print(-1, "The network is not Aig logic.\n");
  }
  int i;
  //Abc_NtkForEachObj(pNtk, pNode, i){
  //  Abc_Print(-2, "node %d type %d \n", Abc_ObjId(pNode), Abc_ObjType(pNode));
  //}
  Abc_Obj_t* pCi;
  Abc_NtkForEachCi(pNtk, pCi, i){
    Abc_Print(-2, "CI: %s %d\n", Abc_ObjName(pCi),Abc_ObjId(pCi));
  }
  Abc_Obj_t* pNode;
  int length=Abc_NtkObjNum(pNtk);
  Abc_Print(-2, "length: %d\n", length);
  bool* window = new bool[length];
  bool* set= new bool[length];
  bool* input= new bool[length];
  coneobj_t* cone = new coneobj_t[length];
  for(i=0;i<length;i++){
    cone[i].node=Abc_NtkObj(pNtk, i);
  }
  Abc_NtkForEachNode(pNtk, pNode, i){
    memset(set, false, length);
    memset(input, false, length);
    for(int j=0;j<length;j++){
      cone[j].out_count=0;
    }
    //find all 
    set[Abc_ObjId(pNode)]=true;
    int res=zerofanout(cone ,i, set, input, length)+1;
    if(res>1){
      window[Abc_ObjId(pNode)]=true;
      int input_num=0;
      for(int j=0;j<length;j++){
        if(input[j])
          input_num++;
      }
      Abc_Print(-2, "XDC %d num %d input %d:\n", Abc_ObjId(pNode),res,input_num);
    }
  }
  DdManager* dd =(DdManager *) Abc_NtkBuildGlobalBdds(pNtk, ABC_INFINITY, 0, 0, 0, 1);
  if(dd==NULL){
    Abc_Print(-1, "build bdd fail\n");
  }
  Abc_NtkForEachNode(pNtk, pNode, i){

  }
  //DdGen *gen;
  //Abc_Print(-2, "variables: %d\n",dd->size);
  //int* cube;
  //CUDD_VALUE_TYPE value;
  //Abc_Obj_t* pCo;
  //Abc_NtkForEachCo(pNtk,pCo, i){
  //  int j;
  //  Abc_NtkForEachNode(pNtk, pNode, j){

  //    //if(Abc_ObjGlobalBdd(pNode)!=NULL){
  //    //  Abc_Print(-2, "node %d has bdd\n", Abc_ObjId(pNode));
  //    //  Cudd_ForeachCube(dd, (DdNode*)Abc_ObjGlobalBdd(pNode), gen,cube,value ){
  //    //    Abc_Print(-2, "cube: ");
  //    //    for(int j=0;j<dd->size;j++){
  //    //      if(cube[j]==0)
  //    //        Abc_Print(-2, "%d ", j);
  //    //      else if(cube[j]==1)
  //    //        Abc_Print(-2, "!%d ", j);
  //    //    }
  //    //    Abc_Print(-2, "\n");
  //    //  }
  //    else{
  //      Abc_Print(-2, "node %d has no bdd\n", Abc_ObjId(pNode));
  //    }
  //  }

  //}
  return 0;
}