#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <string>
#include <cmath>
#include "sat/cnf/cnf.h"
#include "bdd/extrab/extraBdd.h"
#include <list>
#include "lsvCone.h"

//#include "base/abci/b"

extern "C"{
    Aig_Man_t* Abc_NtkToDar( Abc_Ntk_t * pNtk, int fExors, int fRegisters );
    Abc_Ntk_t * Abc_NtkFromGlobalBdds( Abc_Ntk_t * pNtk, int fReverse );
    void Abc_NtkShowBdd( Abc_Ntk_t * pNtk, int fCompl, int fReorder );
}
static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int test_Command(Abc_Frame_t* pAbc, int argc, char** argv);
static int XDC_simp(Abc_Frame_t* pAbc, int argc, char** argv);
static ProgressBar * pProgress;
static int*  pCounter;
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "x", XDC_simp, 1);
  Cmd_CommandAdd(pAbc, "LSV", "test", test_Command, 0);
}
static DdNode * Abc_NodeGlobalBdds_rec( DdManager * dd, Abc_Obj_t * pNode,int * pCounter)
{
    int nBddSizeMax = ABC_INFINITY;
    DdNode * bFunc, * bFunc0, * bFunc1, * bFuncC;
    int fDetectMuxes = 0;
    assert( !Abc_ObjIsComplement(pNode) );
    if ( Cudd_ReadKeys(dd)-Cudd_ReadDead(dd) > (unsigned)nBddSizeMax )
    {
        Extra_ProgressBarStop( pProgress );
        printf( "The number of live nodes reached %d.\n", nBddSizeMax );
        fflush( stdout );
        return NULL;
    }
    // if the result is available return
    if ( Abc_ObjGlobalBdd(pNode) == NULL )
    {
        Abc_Obj_t * pNodeC, * pNode0, * pNode1;
        pNode0 = Abc_ObjFanin0(pNode);
        pNode1 = Abc_ObjFanin1(pNode);
        // check for the special case when it is MUX/EXO
          // compute the result for both branches
        bFunc0 = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin(pNode,0), pCounter ); 
        if ( bFunc0 == NULL )
            return NULL;
        Cudd_Ref( bFunc0 );
        bFunc1 = Abc_NodeGlobalBdds_rec( dd, Abc_ObjFanin(pNode,1), pCounter ); 
        if ( bFunc1 == NULL )
            return NULL;
        Cudd_Ref( bFunc1 );
        bFunc0 = Cudd_NotCond( bFunc0, (int)Abc_ObjFaninC0(pNode) );
        bFunc1 = Cudd_NotCond( bFunc1, (int)Abc_ObjFaninC1(pNode) );
        // get the final result
        bFunc = Cudd_bddAndLimit( dd, bFunc0, bFunc1, nBddSizeMax );
        if ( bFunc == NULL )
            return NULL;
        Cudd_Ref( bFunc );
        Cudd_RecursiveDeref( dd, bFunc0 );
        Cudd_RecursiveDeref( dd, bFunc1 );
        // add the number of used nodes
        (*pCounter)++;
        // set the result
        assert( Abc_ObjGlobalBdd(pNode) == NULL );
        Abc_ObjSetGlobalBdd( pNode, bFunc );
        // increment the progress bar
        if ( pProgress )
            Extra_ProgressBarUpdate( pProgress, *pCounter, NULL );
    }
    // prepare the return value
    bFunc = (DdNode *)Abc_ObjGlobalBdd(pNode);
    // dereference BDD at the node
    return bFunc;
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
int fanout_propagate(DdManager* dd,Abc_Obj_t* pNode){
  int i;
  Abc_Obj_t* pFanout;
  Abc_ObjForEachFanout(pNode, pFanout, i){
    if(Abc_ObjIsCo(pFanout))
      continue;
    else{
      Cudd_RecursiveDeref(dd,(DdNode *)Abc_ObjGlobalBdd(pFanout));
      Abc_NodeGlobalBdds_rec(dd,pNode,pCounter);
    }
    fanout_propagate(dd, pFanout);
  }
  return 0;
}
Abc_Ntk_t* getDC_at_pi(Abc_Ntk_t* pNtk, Abc_Obj_t* pNode, void (*func)(char* argc)){
  int target=Abc_ObjId(pNode);
  Abc_Ntk_t* pNtkNew=Abc_NtkDup(pNtk);
  int i;
  Abc_Obj_t* newpNode=Abc_NtkObj(pNtkNew, Abc_ObjId(pNode));
  Abc_Obj_t * newpi=Abc_NtkCreatePi(pNtkNew);

  Abc_ObjRemoveFanins(newpNode);
  Abc_ObjAddFanin(newpNode, newpi);
  Abc_ObjAddFanin(newpNode,Abc_AigConst1(pNtkNew));
  Abc_Print(-2, "pinum: %d\n", Abc_ObjFaninNum(newpNode));
  DdManager* dd =(DdManager *) Abc_NtkBuildGlobalBdds(pNtkNew, ABC_INFINITY, 0, 0, 0, 1);
  
  if(dd==NULL){
    Abc_Print(-1, "build bdd fail\n");
  }
  DdNode* dccheck=NULL;
  int *sup= new int[dd->size];
  Abc_NtkForEachCo(pNtkNew, pNode, i){
      DdNode* ddnode1=Cudd_Cofactor(dd, (DdNode *)Abc_ObjGlobalBdd(pNode), (DdNode *)Abc_ObjGlobalBdd(newpi));
      Cudd_Ref(ddnode1);
      DdNode* ddnode2=Cudd_Cofactor(dd, (DdNode *)Abc_ObjGlobalBdd(pNode), Cudd_Not((DdNode *)Abc_ObjGlobalBdd(newpi)));
      Cudd_Ref(ddnode2);
      DdNode* dcnode=Cudd_bddXnor(dd, ddnode1, ddnode2);
      Cudd_Ref(dcnode);
      sup=Cudd_SupportIndex(dd, dcnode);
      Abc_Print(-2, "output %d: ",i);
      for(int j=0;j<dd->size;j++){
        Abc_Print(-2, "%d ", sup[j]);
      }
      Abc_Print(-2, "\n");
      Abc_Print(-2, "is 1:%d\n", Cudd_ReadOne(dd)==dcnode);
      if(dccheck==NULL)
        dccheck=dcnode;
      else{
        dccheck=Cudd_bddAnd(dd, dcnode, dccheck);
        Cudd_Ref(dccheck);
      }
  }
  delete[] sup;
  Abc_Print(-2, "dccheck is 1: %d\n", dccheck==Cudd_ReadOne(dd));
  Abc_Print(-2, "variables: %d\n",dd->size);
  DdGen *gen;
  int *cube;
  CUDD_VALUE_TYPE value;
  Cudd_ForeachCube(dd, dccheck, gen,cube,value ){
    Abc_Print(-2, "cube: ");
    for(int j=0;j<dd->size;j++){
      if(cube[j]==0)
        Abc_Print(-2, "%d ", j);
      else if(cube[j]==1)
        Abc_Print(-2, "!%d ", j);
    }
    Abc_Print(-2, "\n");
  }
  //for(int i=0;i<pow(2,dd->size-1);i++){
  //  DdNode* minterm=NULL;
  //  for(int j=0;j<dd->size-1;j++){
  //    if(minterm==NULL){
  //      minterm=Cudd_NotCond(Cudd_bddIthVar(dd, j), !(i>>(dd->size-j-1))&1);
  //    }else{
  //      minterm=Cudd_bddAnd(dd, minterm, Cudd_NotCond(Cudd_bddIthVar(dd, j), !(i>>(dd->size-j-1))&1));
  //    }
  //    Cudd_Ref(minterm);
  //  }
  //  DdNode* result=Cudd_Cofactor(dd, dccheck, minterm);
  //  char a[10]={0};
  //  if(Cudd_bddPickOneCube(dd, minterm, a)==0){
  //    Abc_Print(-2, "pick fail\n");
  //  }
  //  Abc_Print(-2, "cube: ");
  //  for(int j=0;j<dd->size-1;j++){
  //    Abc_Print(-2, "%d ", a[j]);
  //  }
  //  Cudd_Ref(result);
  //  if(result==Cudd_ReadOne(dd)){
  //    Abc_Print(-2, "minterm %d: ", i);
  //  }
  //  if(result==Cudd_Not(Cudd_ReadOne(dd))){
  //    Abc_Print(-2, "dontcare %d: ", i);
  //  }

  //  Cudd_RecursiveDeref(dd, result);
    
  //}
  Cudd_RecursiveDeref(dd, dccheck);
  Abc_Ntk_t* retntk=Abc_NtkFromGlobalBdds(pNtkNew, 0);
  return retntk;
  
}
int XDC_simp(Abc_Frame_t* pAbc, int argc, char** argv){
  int target=47;
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  if(Abc_NtkIsStrash(pNtk)==NULL){
    Abc_Print(-1, "The network is not Aig logic.\n");
  }
  int i;
  //Abc_NtkForEachObj(pNtk, pNode, i){
  //  Abc_Print(-2, "node %d type %d \n", Abc_ObjId(pNode), Abc_ObjType(pNode));
  //}

  Abc_Obj_t* pNode;
  //DdManager* dd =(DdManager *) Abc_NtkBuildGlobalBdds(pNtk, ABC_INFINITY, 0, 0, 0, 1);
  //if(dd==NULL){
  //  Abc_Print(-1, "build bdd fail\n");
  //}
  //int original_size=dd->size;
  //Abc_Print(-2, "variables: %d\n",dd->size);
  Abc_Ntk_t* newntk=getDC_at_pi(pNtk, Abc_NtkObj(pNtk, target));
  

  Abc_FrameReplaceCurrentNetwork( pAbc, newntk );

  //Abc_Print(-2, "ntk type: %d\n",newntk->ntkType);
  //Abc_Ntk_t * pTemp = Abc_NtkIsStrash(pNtk) ? pNtk : Abc_NtkStrash(pNtk, 0, 0, 0);
  //Abc_Print(-2, "pTemp type: %d\n",pTemp->ntkType);
  //Abc_NtkShowBdd(pTemp, 0, 0);
  //if ( pTemp != pNtk )
  //  Abc_NtkDelete( pTemp );
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
static int test_Command(Abc_Frame_t* pAbc, int argc, char** argv){
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int length=Abc_NtkObjNum(pNtk);
  bool* set=new bool[length];
  bool* input=new bool[length];
  for(int i=0;i<length;i++){
    set[i]=false;
    input[i]=false;
  }
  getCone(pNtk,set,input, 7, 3);
  for(int i=0;i<length;i++){
    if(set[i])
      Abc_Print(-2, "node %d\n", i);
  }
  return 0;
}