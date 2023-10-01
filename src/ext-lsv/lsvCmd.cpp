#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "bdd/cudd/cudd.h"
#include <fstream>


//static int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv);
static int LSV_sim_bdd(Abc_Frame_t* pAbc, int argc, char** argv);
static int LSV_sim_aig(Abc_Frame_t* pAbc, int argc, char** argv);
void init(Abc_Frame_t* pAbc) {
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_bdd", LSV_sim_bdd, 0);
  //Cmd_CommandAdd(pAbc, "LSV", "lsv_print_nodes", Lsv_CommandPrintNodes, 0);
  Cmd_CommandAdd(pAbc, "LSV", "lsv_sim_aig", LSV_sim_aig, 0);
}

void destroy(Abc_Frame_t* pAbc) {}


Abc_FrameInitializer_t frame_initializer = {init, destroy};

struct PackageRegistrationManager {
  PackageRegistrationManager() { Abc_FrameAddInitializer(&frame_initializer); }
} lsvPackageRegistrationManager;

//void Lsv_NtkPrintNodes(Abc_Ntk_t* pNtk) {
//  Abc_Obj_t* pObj;
//  int i;
//  Abc_NtkForEachNode(pNtk, pObj, i) {
//    printf("Object Id = %d, name = %s\n", Abc_ObjId(pObj), Abc_ObjName(pObj));
//    Abc_Obj_t* pFanin;
//    int j;
//    Abc_ObjForEachFanin(pObj, pFanin, j) {
//      printf("  Fanin-%d: Id = %d, name = %s\n", j, Abc_ObjId(pFanin),
//             Abc_ObjName(pFanin));
//    }
//    if (Abc_NtkHasSop(pNtk)) {
//      printf("The SOP of this node:\n%s", (char*)pObj->pData);
//    }
//  }
//}

//int Lsv_CommandPrintNodes(Abc_Frame_t* pAbc, int argc, char** argv) {
//  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
//  int c;
//  Extra_UtilGetoptReset();
//  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
//    switch (c) {
//      case 'h':
//        goto usage;
//      default:
//        goto usage;
//    }
//  }
//  if (!pNtk) {
//    Abc_Print(-1, "Empty network.\n");
//    return 1;
//  }
//  Lsv_NtkPrintNodes(pNtk);
//  return 0;
//usage:
//  Abc_Print(-2, "usage: lsv_print_nodes [-h]\n");
//  Abc_Print(-2, "\t        prints the nodes in the network\n");
//  Abc_Print(-2, "\t-h    : print the command usage\n");
//  return 1;
//}

bool LUT(int size,char* query,char** names, bool* values){
  for(int i=0;i<size;i++){
    if(strcmp(query,names[i])==0){
      return values[i];
    }
  }
  assert(false);
}
int LSV_sim_bdd(Abc_Frame_t* pAbc, int argc, char** argv){
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  bool* simValues=new bool[Abc_NtkPiNum(pNtk)];
  char** iNames = new char*[Abc_NtkPiNum(pNtk)];
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }if(argc==1 || argc>2){
    Abc_Print(-2, "usage: lsv_print_nodes <inputs_specification> \n");
    return 1;
  }if(strlen(argv[1])!=Abc_NtkPiNum(pNtk)){
    Abc_Print(-1, "Error: the number of inputs is not equal to the number of PIs.\n");
    return 1;
  }if ( !Abc_NtkIsBddLogic(pNtk) )
  {
      Abc_Print( -1, "Simulating BDDs can only be done for logic BDD networks (run \"collapse\").\n" );
      return 1;
  }
  for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
    simValues[i]=(int)argv[1][i]-48;
  }
  Abc_Obj_t* pPi;
  int i;
  Abc_NtkForEachPi(pNtk, pPi, i){
    iNames[i]=Abc_ObjName(pPi);
  }

  DdManager* ddout = (DdManager *)pNtk->pManFunc;
  //Abc_Print(-2,"%x %x\n",ddout,pNtk);
  Abc_Obj_t* pPo;
  int ithPo;
  Abc_NtkForEachPo(pNtk, pPo, ithPo) {
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo); 
    assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
    DdManager * dd = (DdManager *)pRoot->pNtk->pManFunc;  
    DdNode* ddnode = (DdNode *)pRoot->pData;
    char** vNamesIn = (char**) Abc_NodeGetFaninNames(pRoot)->pArray;
    //Abc_Print(-2,"%x %x %d %d\n",dd,pRoot->pNtk,dd==ddout,pRoot->pNtk==pNtk);
    for(int i=0;i<Abc_ObjFaninNum(pRoot);i++){
      ddnode=Cudd_Cofactor(dd,ddnode,Cudd_NotCond(Cudd_bddIthVar(dd,i),!LUT(Abc_NtkPiNum(pNtk),vNamesIn[i],iNames,simValues)));
    }
    Abc_Print(-2,Abc_ObjName(pPo));
    Abc_Print(-2,": ");
    if(Cudd_IsConstant(ddnode)){
      if(ddnode==Cudd_ReadOne(dd)){
        Abc_Print(-2,"1");
      }else{
        Abc_Print(-2,"0");
      }
    }else{
      Abc_Print(-2,"-");
    }
    Abc_Print(-2,"\n");
  } 
  //Abc_Print(-2,"\n");

  // obtain all primary inputs
  ////////////////////////// for debug //////////////////////////
  //Abc_Print(-2,"Inputnum: ");
  //Abc_Print(-2,int_to_char(Abc_NtkPiNum(pNtk)));
  ////////////////////////// for debug //////////////////////////
    
  
  //for(int i=1;i<Abc_NtkPiNum(pNtk);i++){
  //  dVar[0]=Cudd_Cofactor(dd,dVar[0],dVar[i]);
  //  Abc_Print(-2,"%d %d\n",Cudd_IsConstant(dVar[0]),dVar[0]==Cudd_ReadOne(dd));
  //}
  //dVar[0]=Cudd_Cofactor(dd,dVar[0],dVar[0]);
  //Abc_Print(-2,"%d %d\n",Cudd_IsConstant(dVar[0]),dVar[0]==Cudd_ReadOne(dd));
  //Abc_Print(-2,"%x\n",dd);
  //Abc_Obj_t* pPo;
  //int ithPo;
  //Abc_NtkForEachPo(pNtk, pPo, ithPo) {
  //  Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo); 
  //  assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
  //  DdManager* ddm = (DdManager *)pNtk->pManFunc;
  //  DdNode* ddnode = (DdNode *)pRoot->pData;
  //  int faninNum=Abc_ObjFaninNum(pRoot);
  //  for(int i=0;i<faninNum;i++){
  //    Abc_Print(-2,"%d ",Cudd_bddIthVar(ddm,i)==Cudd_bddIthVar(dd,i));
  //  }
  //  Abc_Print(-2,"%x %d\n",dd,dd==ddm);
  //}
  /*DdNode** dVar=new DdNode* [Abc_NtkPiNum(pNtk)]; 
  DdManager* dd = (DdManager *)pNtk->pManFunc;
  for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
    dVar[i]=Cudd_NotCond(Cudd_ReadVars(dd,i),!simValues[i]);
    if(dVar[i]==NULL){
      Abc_Print(-2,"Error: dVar[%d] is NULL.\n",i);
      return 1;
    }
  }
  

  Abc_Obj_t* pPi; 
  int i;
  Abc_NtkForEachObj(pNtk, pPi, i){
    Abc_Print(-2,Abc_ObjName(pPi));
    Abc_Print(-2,":");
    Abc_Print(-2,"%d",(Abc_ObjId(pPi)));
    Abc_Print(-2,"\n");
  }

  Abc_Obj_t * pPo;
  int ithPo;
  Abc_NtkForEachPo(pNtk, pPo, ithPo) {
    Abc_Obj_t* pRoot = Abc_ObjFanin0(pPo); 
    assert( Abc_NtkIsBddLogic(pRoot->pNtk) );
    DdNode* ddnode = (DdNode *)pRoot->pData;
    for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
      ddnode=Cudd_Cofactor(dd,ddnode,dVar[i]);
    }
    Abc_Print(-2,"\n");
    Abc_Print(-2,Abc_ObjName(pPo));
    Abc_Print(-2,": ");
    if(Cudd_IsConstant(ddnode)){
      if(ddnode==Cudd_ReadOne(dd)){
        Abc_Print(-2,"1");
      }else{
        Abc_Print(-2,"0");
      }
    }else{
      Abc_Print(-2,"-");
    }
    //Abc_Print(-2, "Root name: ");
    //Abc_Print(-2, Abc_ObjName(pRoot));
    //Abc_Print(-2, "\n");
  }*/

  return 0;
}



















int LSV_sim_aig(Abc_Frame_t* pAbc, int argc, char** argv){
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  std::ifstream file;
  file.open(argv[1]);
  std::string line;
  bool** outValue=new bool*[Abc_NtkObjNum(pNtk)];
  for(int i=0;i<Abc_NtkObjNum(pNtk);i++){
    outValue[i]=new bool[1000000];
  }
  int outLen=0;
  //int i;
  //Abc_Obj_t* pNode;
  //Abc_NtkForEachObj(pNtk, pNode, i){
  //  Abc_Print(-2,Abc_ObjName(pNode));
  //  Abc_Print(-2,", ");
  //  Abc_Print(-2,"%d",Abc_ObjId(pNode));
  //  Abc_Print(-2,": ");
  //  Abc_Obj_t* pFanin;
  //  int j;
  //  Abc_ObjForEachFanin(pNode, pFanin, j){
  //    Abc_Print(-2,Abc_ObjName(pFanin));
  //  }
  //  Abc_Print(-2,"\n");
  //}
  //Abc_Print(-2,"\n");
  
  while (file>>line)
  {
    bool* simValues=new bool[Abc_NtkPiNum(pNtk)];
    bool* nodeValues=new bool[Vec_PtrSize((pNtk)->vObjs)];
    *nodeValues={0};
    *simValues={0};
    for(int i=0;i<Abc_NtkPiNum(pNtk);i++){
      simValues[i]=(int)line[i]-48;
    //  if(simValues[i]){
    //    Abc_Print(-2,"1");
    //  }else{
    //    Abc_Print(-2,"0");
    //  }
    }
    //Abc_Print(-2,"\n");
    int i;
    Abc_Obj_t* pNode;
    Abc_NtkForEachPi(pNtk, pNode, i){
      nodeValues[Abc_ObjId(pNode)]=simValues[i];
      //Abc_Print(-2,Abc_ObjName(pNode));
      //Abc_Print(-2,": ");
      //Abc_Print(-2,"%d",nodeValues[Abc_ObjId(pNode)]);
      //Abc_Print(-2,"\n");
    }
    Abc_NtkForEachNode(pNtk, pNode, i){
      Abc_Obj_t* pFanin;
      nodeValues[Abc_ObjId(pNode)]=(nodeValues[Abc_ObjId(Abc_ObjFanin0(pNode))]^Abc_ObjFaninC0(pNode)) & (nodeValues[Abc_ObjId(Abc_ObjFanin1(pNode))]^Abc_ObjFaninC1(pNode));
      //Abc_Print(-2,Abc_ObjName(pNode));
      //Abc_Print(-2,": ");
      //Abc_Print(-2,"%d",nodeValues[Abc_ObjId(pNode)]);
      //Abc_Print(-2," ");
      //Abc_Print(-2,Abc_ObjName(Abc_ObjFanin0(pNode)));
      //Abc_Print(-2,": ");
      //Abc_Print(-2,"%d\'%d",nodeValues[Abc_ObjId(Abc_ObjFanin0(pNode))],Abc_ObjFaninC0(pNode));
      //Abc_Print(-2," ");
      //Abc_Print(-2,Abc_ObjName(Abc_ObjFanin1(pNode)));
      //Abc_Print(-2,": ");
      //Abc_Print(-2,"%d\'%d",nodeValues[Abc_ObjId(Abc_ObjFanin1(pNode))],Abc_ObjFaninC1(pNode));
      //Abc_Print(-2,"\n");
    }
    Abc_NtkForEachPo(pNtk, pNode, i){
      //Abc_Print(-2,Abc_ObjName(pNode));
      //Abc_Print(-2,": ");
      //if(nodeValues[Abc_ObjId(Abc_ObjFanin0(pNode))]^Abc_ObjFaninC0(pNode)){
      //  outValue[i][outLen]=1;
      //}else{
      //  outValue[i][outLen]=0;
      //}
      outValue[i][outLen]=(nodeValues[Abc_ObjId(Abc_ObjFanin0(pNode))]^Abc_ObjFaninC0(pNode));
    }
    //Abc_Print(-2,"\n");
    delete [] nodeValues;
    delete [] simValues;
    outLen++;
  }
  for(int i=0;i<Abc_NtkPoNum(pNtk);i++){
    Abc_Print(-2,Abc_ObjName(Abc_NtkPo(pNtk,i)));
    Abc_Print(-2,": ");
    for(int j=0;j<outLen;j++){
      if(outValue[i][j]){
        Abc_Print(-2,"1");
      }else{
        Abc_Print(-2,"0");
      }
    }
    Abc_Print(-2,"\n");
  }
  for(int i=0;i<outLen;i++){
    delete  [] outValue [i];
  }
  return 0;
}