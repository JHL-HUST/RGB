//Copyright <2021> <Hua Jiang(huajiang@ynu.edu.cn)>
//
//Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
//
//The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
//
//THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

/*
 *
 * g++ -O3 -DALL KpLeX-2021.cpp -o KpLeX -std=c++11 
 * usage: ./KpLeX instance -x k
 *     
 */
#include "MBitSet.h"
#include "MGraph.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <sys/times.h>
#include <sys/types.h>
#include <limits.h>
#include <unistd.h>
#include <sys/resource.h>
#include <math.h>
#include <assert.h>
#include <bitset>
#include <iostream>

#define WORD_LENGTH 100
#define TRUE 1
#define FALSE 0
#define NONE -1
#define DELIMITER 0
#define PASSIVE 0
#define ACTIVE 1
#define P_TRUE 2
#define P_FALSE 0
#define NO_REASON -3
#define CONFLICT -1978
#define MAX_NODE 80000000
#define max_expand_depth 100000
#define pop(stack) stack[--stack ## _fill_pointer]
#define push(item, stack) stack[stack ## _fill_pointer++] = item
#define ptr(stack) stack ## _fill_pointer
#define is_neibor(i,j) matrice[i][j]

#define CUR_KPX_SIZE Clique_Stack_fill_pointer
#define CURSOR Cursor_Stack[Cursor_Stack_fill_pointer-1]
#define MIN(a,b) a<=b?a:b
#define BIT_MAP_SIZE 4097

#define SET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) |= (1 << ((col) & 7)))
#define GET_EDGE(row,col) ((*(Adj_Matrix + (row)* MATRIX_ROW_WIDTH + ((col) >> 3))) & (1 << ((col) & 7)))

#define iMatrix(i) (Adj_Matrix+(i)*MATRIX_ROW_WIDTH)
#define Matrix(i,j) ((*((i) + ((j) >> 3))) & (1 << ((j) & 7)))
#define is_adj(u,v) (u>v? ((Matrix[u][v]>>1)%2) : ((Matrix[v][u]>>1)%2))
#define nbOfcn(u,v) (u>v? (Matrix[u][v]>>2) : (Matrix[v][u]>>2))
#define is_consistent(u,v) (u>v? (1-Matrix[u][v]%2) : (1-Matrix[v][u]%2))
#define is_conflicting(u,v) (u>v? (Matrix[u][v]%2) : (Matrix[v][u]%2))
using namespace std;

static int TIME_OUT, CUT_OFF=0;
static double BEST_SOL_TIME;

static int FORMAT = 1, NB_NODE, NB_NODE_O, ADDED_NODE, NB_EDGE, NB_EDGE_O,
		MAX_KPX_SIZE, MAX_ISET_SIZE, INIT_KPX_SIZE, HEUR_KPX_SIZE,
  NB_BACK_CLIQUE, MATRIX_ROW_WIDTH, MAX_VERTEX_NO, K_CORE_G = 0, Reasoning_Point=0,MAX_MATRIX_SIZE=2000;

#define CORE_NO Vertex_UB
static int Max_Degree = 0, UPPER_BOUND=0;
static int Node_Degree[MAX_NODE];
static int *CNN;


std::bitset<MAX_NODE> Node_State;
std::bitset<MAX_NODE> Node_State2;


static int **Node_Neibors;

static int Candidate_Stack_fill_pointer = 0;
static int Candidate_Stack[MAX_NODE * 2];
static int Vertex_UB[MAX_NODE * 2];
static int NBNN_Stack_fill_pointer = 0;
static char NBNN_Stack[MAX_NODE*2];
static int Clique_Stack_fill_pointer,Energy_Stack_fill_pointer;
static int  *Clique_Stack, *MaxCLQ_Stack, *Energy_Stack;
static int Cursor_Stack[max_expand_depth];
static int Cursor_Stack_fill_pointer = 0;
  
static int *Node_Reason;
static int ** Matrix;
static unsigned char * Adj_Matrix;

static int iSET_COUNT = 0;
static int *iSET_Size;
static char *iSET_State;
static char *iSET_Used;
static char *iSET_Tested;
static int *iSET_Index;
static char *iSET_Involved;
static char *Is_Tested;
static int **iSET;

static int *REASON_STACK;
static int REASON_STACK_fill_pointer = 0;
static int *CONFLICT_ISET_STACK;
static int CONFLICT_ISET_STACK_fill_pointer;
static int *ADDED_NODE_iSET;
static int *REDUCED_iSET_STACK = Node_Degree;
static int REDUCED_iSET_STACK_fill_pointer = 0;
static int *PASSIVE_iSET_STACK;
static int PASSIVE_iSET_STACK_fill_pointer = 0;
static int *FIXED_NODE_STACK;
static int FIXED_NODE_STACK_fill_pointer = 0;
static int *UNIT_STACK;
static int UNIT_STACK_fill_pointer = 0;
static int *NEW_UNIT_STACK;
static int NEW_UNIT_STACK_fill_pointer = 0;

static int Rollback_Point;
static int Branching_Point;
//static int Matrix_Reallocation = 0;
static int *Old_Name;
static int *Second_Name;
static int NB_CANDIDATE = 0, FIRST_INDEX;
static int START_MAXSAT_THD = 15;

static int Extra_Node_Stack_fill_pointer = 0;
static int Extra_Node_Stack[1000000];

static int Last_Idx = 0;
static int cut_ver = 0, total_cut_ver = 0;
static int cut_inc = 0, total_cut_inc = 0;
static int cut_iset = 0, total_cut_iset = 0;
static int cut_satz = 0, total_cut_satz = 0;
static long long Branches_Nodes[6];
static int LAST_IN;
static float Dynamic_Radio = 0.70;
static int REBUILD_MATRIX = FALSE;
static int CUR_MAX_NODE;
static int Branches[1200];
static int * Init_Adj_List;
static int BLOCK_COUNT = 0;
static int *BLOCK_LIST[100];
static double READ_TIME, INIT_TIME, SEARCH_TIME;
static long long N0_0 = 0, N0_1 = 0, N1_0 = 0, N1_1 = 0, L1 = 0;
static double D0 = 0, D1 = 0, D2 = 0, Dt = 0;

int last_node;

typedef struct {
	MBitSet64 bitcolor;
	unsigned int *vertices;
  unsigned int *index;
	int sz;
}ColorType;
ColorType *colors;

MCsrGraph kernalG;
MBitGraph *bg;

int OPT = 0;
int *target_normal, *target_abnormal;
int max_node_index;
int **Cand_wrt_nb;
int **Cand_wrt_nb2;
int *Candidate_Stack2;
int *NBNN_Stack2;
int *selected;
//long long *selected_step;// = new long long[2*MAX_NODE];

struct Paramerters{
  int KX;
  int ORDER;
  int FORMAT;
  int START_MAXSAT_THD;
  int CUT_OFF;
  int TIME_OUT;
}PARA;

static double get_utime() {
	struct rusage utime;
	getrusage(RUSAGE_SELF, &utime);
	return (double) (utime.ru_utime.tv_sec
			+ (double) utime.ru_utime.tv_usec / 1000000);
}

static int int_cmp_desc(const void * a, const void * b) {
	return *((int *) b) - *((int *) a);
}


static int int_cmp_asc(const void * a, const void * b) {
	return *((int *) a) - *((int *) b);
}
static int is_adjacent(int node1, int node2) {
  int neibor, *neibors;
  if(node1>node2){
    neibors = Node_Neibors[node1];
  }else{
    neibors = Node_Neibors[node2];
    node2=node1;
  }
  for (neibor = *neibors; neibor <node2 && neibor!=NONE ; neibor = *(++neibors));
  return neibor==node2;
}

static int nbE=0;

static void allcoate_memory_for_adjacency_list(int nb_node, int nb_edge,
		int offset) {
	int i, block_size = 40960000, free_size = 0;
	Init_Adj_List = (int *) malloc((2 * nb_edge + nb_node) * sizeof(int));
	if (Init_Adj_List == NULL ) {
		for (i = 1; i <= NB_NODE; i++) {
			if (Node_Degree[i - offset] + 1 > free_size) {
				Node_Neibors[i] = (int *) malloc(block_size * sizeof(int));
				BLOCK_LIST[BLOCK_COUNT++] = Node_Neibors[i];
				free_size = block_size - (Node_Degree[i - offset] + 1);
			} else {
				Node_Neibors[i] = Node_Neibors[i - 1]
						+ Node_Degree[i - 1 - offset] + 1;
				free_size = free_size - (Node_Degree[i - offset] + 1);
			}
		}
	} else {
		BLOCK_COUNT = 1;
		BLOCK_LIST[BLOCK_COUNT - 1] = Init_Adj_List;
		Node_Neibors[1] = Init_Adj_List;
		for (i = 2; i <= NB_NODE; i++) {
			Node_Neibors[i] = Node_Neibors[i - 1] + Node_Degree[i - 1 - offset]
					+ 1;
		}
	}
}

static int read_graph_node_node(char *input_file, int format) {
  int j, l_node, r_node, nb_edge = 0, max_node = NONE, offset = 0;
  int node = 1;
  char line[128], word[10];
  FILE* fp_in = fopen(input_file, "r");
  
  if (fp_in == NULL ) {
    printf("R can not open file %s\n", input_file);
    return FALSE;
  }

  if (format == 1)
    printf("R reading file <e n1 n2> ...\n");
  else
    printf("R reading file <n1 n2> ...\n");

  memset(Node_Degree, 0, MAX_NODE*sizeof(int));

  while (fgets(line, 127, fp_in) != NULL ) {
    if ((format == 1 && line[0] == 'e')
	|| (format == 2 && line[0] != '%')) {
      if (format == 1)
	sscanf(line, "%s%d%d", word, &l_node, &r_node);
      else
	sscanf(line, "%d%d", &l_node, &r_node);
      if (l_node >= 0 && r_node >= 0 && l_node != r_node) {

	nb_edge++;			    

	if (l_node > max_node)
	  max_node = l_node;
	if (r_node > max_node)
	  max_node = r_node;

	if (offset ==0 && (l_node == 0 || r_node == 0)){
	  offset = 1;
	}
	
	if (max_node+offset>=MAX_NODE) {
	  printf("! The graph goes beyond the maximum size (%d) can be processed.\n",MAX_NODE);
	  printf("! Please modify the definition of the variable MAX_NODE to fit the size.\n");
	  exit(1);
	}
	
	Node_Degree[l_node]++;
	Node_Degree[r_node]++;

      }
    }
  }
  NB_NODE = max_node;
  NB_NODE = NB_NODE + offset;

  printf("R the graph size is %d\n", NB_NODE);
	
  Node_Neibors = (int **) malloc((NB_NODE + 1) * sizeof(int *));
  allcoate_memory_for_adjacency_list(NB_NODE, nb_edge, offset);
  memset(Node_Degree, 0, (NB_NODE + 1) * sizeof(int));

  nb_edge = 0;
  fseek(fp_in, 0L, SEEK_SET);
  while (fgets(line, 127, fp_in) != NULL ) {
    if ((format == 1 && line[0] == 'e')
	|| (format == 2 && line[0] != '%')) {
      if (format == 1)
	sscanf(line, "%s%d%d", word, &l_node, &r_node);
      else
	sscanf(line, "%d%d", &l_node, &r_node);
      if (l_node >= 0 && r_node >= 0 && l_node != r_node) {
	if(offset){
	  l_node +=offset;
	  r_node +=offset;
	}
	for (j = 0; j < Node_Degree[l_node]; j++) {
	  if (Node_Neibors[l_node][j] == r_node)
	    break;
	}
	if (j == Node_Degree[l_node]) {
	  Node_Neibors[l_node][Node_Degree[l_node]] = r_node;
	  Node_Neibors[r_node][Node_Degree[r_node]] = l_node;
	  Node_Degree[l_node]++;
	  Node_Degree[r_node]++;
	  nb_edge++;
	}
      }
    }
  }
  NB_EDGE = nb_edge;
  Max_Degree = 0;
  N0_0 = NB_NODE;
  for (node = 1; node <= NB_NODE; node++) {
    Node_Neibors[node][Node_Degree[node]] = NONE;

    if (Node_Degree[node] > Max_Degree)
      Max_Degree = Node_Degree[node];
  }
  UPPER_BOUND=Max_Degree+PARA.KX;
  return TRUE;
}

static int build_simple_graph_instance(char *input_file) {
  printf("# reading instance ...\n");
  char * fileStyle="clq";
  if(strrchr(input_file, '.')!=NULL)
    fileStyle = strrchr(input_file, '.') + 1;
    
	if (strcmp(fileStyle, "clq") == 0) {
	  read_graph_node_node(input_file, 1);
	} else if (strcmp(fileStyle, "edges") == 0) {
	  read_graph_node_node(input_file, 2);
	} else if (strcmp(fileStyle, "mtx") == 0) {
		read_graph_node_node(input_file, 2);
	} else if (FORMAT == 1) {
		read_graph_node_node(input_file, 1);
	} else if (FORMAT == 2) {
		read_graph_node_node(input_file, 2);
	} else {
		read_graph_node_node(input_file, 1);
	}
	printf("R Instance Information: #node=%d #edge=%d density=%9.8f\n", NB_NODE,
			NB_EDGE, ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1)));
	NB_NODE_O = NB_NODE;
	NB_EDGE_O = NB_EDGE;
	D0 = ((float) NB_EDGE * 2 / NB_NODE / (NB_NODE - 1));

	READ_TIME = get_utime();
	printf("R the reading time is %4.2lf \n", READ_TIME);
	return TRUE;
}

static int sort_by_degeneracy_ordering() {
	int *degree_counter, *where;
	int p1, i, node = NONE, neibor, *neibors, t, j, h, k;
	int cur_degree = 0;
	INIT_KPX_SIZE = 0;
	printf("I computing an initial k-plex...\n");

	where = Candidate_Stack + NB_NODE + 1;
	degree_counter = Vertex_UB + NB_NODE + 1;
	memset(degree_counter, 0, (Max_Degree + 1) * sizeof(int));
	
	for (node = 1; node <= NB_NODE; node++) {
	  CORE_NO[node]=Node_Degree[node];
	  degree_counter[Node_Degree[node]]++;
	}
	j = 0;
	for (i = 0; i <= Max_Degree; i++) {
		k = degree_counter[i];
		degree_counter[i] = j;
		j += k;
	}

	for (node = 1; node <= NB_NODE; node++) {
		Candidate_Stack[t = degree_counter[Node_Degree[node]]++] = node;
		where[node] = t;
	}
	
	for (i = Max_Degree; i > 0; i--) {
		degree_counter[i] = degree_counter[i - 1];
	}
	degree_counter[0] = 0;

	Candidate_Stack[NB_NODE] = DELIMITER;
	ptr(Candidate_Stack) = NB_NODE + 1;

	p1 = 0;
	cur_degree = Node_Degree[Candidate_Stack[p1]];
	while (p1 < NB_NODE) {
		node = Candidate_Stack[p1];

		if (cur_degree > K_CORE_G)
			K_CORE_G = cur_degree;

		if (p1 < NB_NODE - 1
				&& Node_Degree[node] == Node_Degree[Candidate_Stack[p1 + 1]]) {
			degree_counter[Node_Degree[node]] = p1 + 1;
		}
		if (Node_Degree[node] > MAX_VERTEX_NO)
			MAX_VERTEX_NO = Node_Degree[node];

		if (Node_Degree[node] >= NB_NODE - p1 - PARA.KX) { //when KX=1, the remain ing is a clique.
		  BEST_SOL_TIME=get_utime();
		  MAX_KPX_SIZE=HEUR_KPX_SIZE=INIT_KPX_SIZE = NB_NODE - p1;
		  printf("I the upper bound of k-plex %d ...\nI the initial %d-plex  %d...\n", UPPER_BOUND, PARA.KX,INIT_KPX_SIZE);
		  MaxCLQ_Stack = (int *) malloc((UPPER_BOUND+1) * sizeof(int));
		  Clique_Stack = (int *) malloc((UPPER_BOUND+1) * sizeof(int));
		  Energy_Stack = (int *) malloc((UPPER_BOUND+1) * sizeof(int));
		  memcpy(MaxCLQ_Stack, Candidate_Stack + p1,INIT_KPX_SIZE * sizeof(int));
		  break;
		}

		neibors = Node_Neibors[node];
		for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
			if (where[neibor] > p1) {
				t = where[neibor];
				h = degree_counter[Node_Degree[neibor]];

				k = Candidate_Stack[h];

				Candidate_Stack[h] = neibor;
				where[neibor] = h;

				Candidate_Stack[t] = k;
				where[k] = t;

				degree_counter[Node_Degree[neibor]]++;

				Node_Degree[neibor]--;
				if (Node_Degree[neibor]
						!= Node_Degree[Candidate_Stack[h - 1]]) {
					degree_counter[Node_Degree[neibor]] = h;
				}
			}
		}
		p1++;
	}

	if (UPPER_BOUND == INIT_KPX_SIZE) {
		MAX_KPX_SIZE = INIT_KPX_SIZE;
		printf("I find the maximum %d-plex in initial phase!\n",PARA.KX);
		return TRUE;
	} else {
		return FALSE;
	}
}




static long long BRANCHING_COUNT = 0;

static void store_maximum_clique(int node, int silent) {
	if (Reasoning_Point == 0)
	  push(node, Clique_Stack);
	else
	  push(Second_Name[node], Clique_Stack);

	MAX_KPX_SIZE = ptr(Clique_Stack);
        BEST_SOL_TIME=get_utime();
	memcpy(MaxCLQ_Stack, Clique_Stack, MAX_KPX_SIZE * sizeof(int));
	
	ptr(NBNN_Stack) = ptr(Candidate_Stack) = NB_NODE + 1;
	ptr(Cursor_Stack) = 1;
	ptr(Clique_Stack) = 0;
	ptr(Energy_Stack) =0;
	Rollback_Point = 0;
	Reasoning_Point=0;
	Vertex_UB[CURSOR]=MAX_KPX_SIZE;
	if (silent==0)
		printf("C %4d |%7d |%14lld| %8.2lf\n", MAX_KPX_SIZE, CURSOR,BRANCHING_COUNT,BEST_SOL_TIME);
	total_cut_ver += cut_ver;
	cut_ver = 0;
	total_cut_inc += cut_inc;
	cut_inc = 0;
	total_cut_iset += cut_iset;
	cut_iset = 0;
        total_cut_satz += cut_satz;
        cut_satz = 0;
	Last_Idx = CURSOR;
}

static long long cut_level=0;
static long long cut_count=0;

static float BMTHD=0.3;

static inline void reset_state(){
  for(int i=CURSOR+1, cn=Candidate_Stack[i];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    Node_State.reset(cn);
    Node_State2.reset(cn);
  }
}


static inline void reset_state1(){
 for(int i=0;i<ptr(Clique_Stack);i++){
      if(Energy_Stack[i]<0){
	Energy_Stack[i]=-Energy_Stack[i]-1;
      }
 }
 for(int i=CURSOR+1, cn=Candidate_Stack[i];cn!=DELIMITER;cn=Candidate_Stack[++i]){
   Node_State.reset(cn);
   Node_State2.reset(cn);
 }
}
static inline void reset_state2(){
   for(int i=0;i<ptr(Clique_Stack);i++){
      if(Energy_Stack[i]<0){
	Energy_Stack[i]=-Energy_Stack[i]-1;
      }
   }
}


static int produce_subgraph0() {
  int i = CURSOR,j=0, neibor, max = 0, *neibors,*neibors2;

  int start=ptr(Candidate_Stack);
  
  int bnode=Candidate_Stack[CURSOR];
  last_node = bnode;
  assert(ptr(Candidate_Stack) == ptr(NBNN_Stack));
  
  for(int cn=Candidate_Stack[i=CURSOR+1];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    Node_State.reset(cn);
    Node_State2.set(cn);
    // CNN[cn]=0;
  }
  //mark neighbors of current branching vertex,and set state
  neibors = Node_Neibors[bnode];
  for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
    if(Node_State2[neibor])
      Node_State.set(neibor);
  }
  
  NB_CANDIDATE=0;
  for(int cn=Candidate_Stack[i=CURSOR+1];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    assert(cn!=bnode);
    if(Node_State[cn]){
      push(cn, Candidate_Stack);
      push(NBNN_Stack[i],NBNN_Stack);
      NB_CANDIDATE++;
    }else if((NBNN_Stack[CURSOR]<PARA.KX-1) &&  ( NBNN_Stack[i]<PARA.KX-1)){
      push(cn, Candidate_Stack);
      push(NBNN_Stack[i]+1,NBNN_Stack);
      NB_CANDIDATE++;
    }
  }
  push(DELIMITER, Candidate_Stack);
  push(DELIMITER, NBNN_Stack);
  // check_candidates3();

  if(NB_CANDIDATE+CUR_KPX_SIZE<=MAX_KPX_SIZE){
    reset_state();
    return 0;
  }
  
  for(int cn=Candidate_Stack[i=CURSOR+1];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    Node_State.reset(cn);
    Node_State2.reset(cn);
  }
  
  for(int cn=Candidate_Stack[j=start];cn!=DELIMITER;cn=Candidate_Stack[++j]){
    Node_State2.set(cn);
  }
  
  //-----------------------------//
 
  int count=0;
  for(i=0;i<ptr(Clique_Stack)-1;i++){
    if(is_adjacent(Clique_Stack[i],bnode)==FALSE){
      assert(Energy_Stack[i]<PARA.KX-1);
      Energy_Stack[i]=-(Energy_Stack[i]+1);
      count++;
    }
  }
  assert(count==NBNN_Stack[CURSOR]);
  assert(ptr(Candidate_Stack) == ptr(NBNN_Stack));
 
  for(i=0;i<ptr(Clique_Stack)-1;i++){
    assert(Energy_Stack[i]<PARA.KX);
    if((Energy_Stack[i]<0 && (Energy_Stack[i] == 1-PARA.KX))){
      int nn=Clique_Stack[i];

      neibors = Node_Neibors[nn];
      for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
        if(Node_State2[neibor])
	  Node_State.set(neibor);
      }
      
      for(int cn=Candidate_Stack[j=start];cn!=DELIMITER;cn=Candidate_Stack[++j]){
	 assert(nn!=cn || nn+cn!=0);
         if(cn>0 && Node_State[cn]==0){
	   Candidate_Stack[j]=-cn;
	   NB_CANDIDATE--;
	 }
      }

      neibors = Node_Neibors[nn];
      for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
        if(Node_State2[neibor])
	  Node_State.reset(neibor);
      }
      
      if(NB_CANDIDATE+CUR_KPX_SIZE<=MAX_KPX_SIZE){
	 for(int cn=Candidate_Stack[j=start];cn!=DELIMITER;cn=Candidate_Stack[++j]){
	   if(cn>0)
	     Node_State2.reset(cn);
	   else
	     Node_State2.reset(-cn);
	 }
	 for(int i=0;i<ptr(Clique_Stack);i++){
            if(Energy_Stack[i]<0){
	     Energy_Stack[i]=-Energy_Stack[i]-1;
	    }
	 }
      
	 return 0;
      }
    }
  }

 
  int _count=0;
  i=j=start;
  for(int cn=Candidate_Stack[i];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    if(cn>0){
       #if !defined(COMM) && !defined(ALL)
        Node_State2.reset(cn);
	#endif
        Candidate_Stack[j]=cn;
        NBNN_Stack[j]=NBNN_Stack[i];
	_count++;
	j++;
    }else{
       Node_State2.reset(-cn);
    }
  }
  assert(_count==NB_CANDIDATE);
  Candidate_Stack[j]=DELIMITER;
  NBNN_Stack[j]=DELIMITER;
  ptr(Candidate_Stack)=j+1;
  ptr(NBNN_Stack)=j+1;

  if(NB_CANDIDATE+CUR_KPX_SIZE>MAX_KPX_SIZE){

    #if !defined(COMM) && !defined(ALL)
    for(i=0;i<ptr(Clique_Stack);i++){
         if(Energy_Stack[i]<0){
	   Energy_Stack[i]=-Energy_Stack[i];
	 }
    }
    #endif
    
    return ptr(Candidate_Stack)-1-(MAX_KPX_SIZE-CUR_KPX_SIZE);
  }else{
    reset_state1();
    return 0;
  }
}


static int cut_by_iteration_partition(){
  int ub=0,k=ptr(Candidate_Stack)-1;
  int lb=MAX_KPX_SIZE - CUR_KPX_SIZE;
  int min_k;
  assert(Candidate_Stack[k]==DELIMITER);
  
  #ifdef INVE
    for(int i=ptr(Clique_Stack)-1;i>=0;i--){
  #else
    for(int i=0;i<ptr(Clique_Stack);i++){
  #endif
    int cnode=Clique_Stack[i];
    int ub1=PARA.KX-1 - Energy_Stack[i];
    assert(ub1>=0);
    if(ub1==0)continue;
    int j=k-1,p=k,count=0;
    for(int pnode=Candidate_Stack[j];pnode!=DELIMITER;pnode=Candidate_Stack[--j]){
      if(NBNN_Stack[j] == 0)  continue;
      if(is_adjacent(cnode,pnode)==FALSE){
      	if(j<p-1){
        	int temp=Candidate_Stack[p-1];
        	Candidate_Stack[p-1]=pnode;
        	Candidate_Stack[j]=temp;
        	temp=NBNN_Stack[p-1];
        	NBNN_Stack[p-1]=NBNN_Stack[j];
        	NBNN_Stack[j]=temp;
      	}
      	p--;
      	count++;
      }
    }
    assert(j<p);
    assert(Candidate_Stack[j]==DELIMITER);
    
    min_k=j;
    
    if(count<ub1)
      ub1=count;
  
    if(ub+ub1<=lb){
      ub=ub+ub1;
      k=p;
      if(k==min_k+1)
	      break;
    }else{
       return k-(lb-ub) > min_k ? k-(lb-ub): min_k+1;
    }
  }  
  if(k==min_k+1){
    return k;
  }
  else{
    assert(k>min_k+1);
    return k-(lb-ub) > min_k ? k-(lb-ub): min_k+1;
  }
}

inline int intsecColor(unsigned int u, int c) {
	return colors[c].bitcolor.intersect(*(bg->rows[u]));
}

static int cut_by_zjz(int start){
  if (Branching_Point == start)  return start;
  int ub=0,kk=ptr(Candidate_Stack)-1;
  int lb=MAX_KPX_SIZE - CUR_KPX_SIZE;
  
  int i, j;
  
  int selected_num = 0;
  for (i = start; i < kk; i++)
    selected[i] = 0;
  
  int counts[PARA.KX];
  for (i=0;i<PARA.KX;++i){
    counts[i]=0;
  }
  for(int cn=Candidate_Stack[i=start];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    int nb = NBNN_Stack[i];
    Cand_wrt_nb[nb][counts[nb]] = i;
    Cand_wrt_nb2[nb][counts[nb]++] = i;
  }
  int org_counts[PARA.KX];
  for (i=0;i<PARA.KX;++i){
    org_counts[i]=counts[i];
  }
  int maxcolor;
  for (int t = PARA.KX-1; t >= 0; t--){
    int num = counts[t];
    if (num == 0)
      continue;
    int *nodes = Cand_wrt_nb[t];
		maxcolor = 1;
		colors[1].sz = 0; colors[1].bitcolor.clear(); colors[2].sz = 0; colors[2].bitcolor.clear();
		for (i = 0; i < num; i++) {
			int u = nodes[i];
			int c = 1;
			while (1) {
				int con = intsecColor(target_normal[Candidate_Stack[u]]-1, c);
				if (con == 0) {
					break;
				}else
					c++;
			}
			colors[c].bitcolor.set(target_normal[Candidate_Stack[u]]-1);
			colors[c].vertices[colors[c].sz] = target_normal[Candidate_Stack[u]]-1;
      colors[c].index[colors[c].sz] = u;
			colors[c].sz++;		
			if (c > maxcolor) {
				maxcolor = c;
				colors[maxcolor + 1].bitcolor.clear();
				colors[maxcolor + 1].sz = 0;
			}
		}
   
    for (i = 1; i <= maxcolor; i++){
      int insert[PARA.KX-t];
      int insert_num = 0;
      for (j = 0; j < t; j++){
        if (counts[j] == 0)
          continue;
        for (int l = 0; l < counts[j]; l++){
          int node = Cand_wrt_nb[j][l];
          int con = intsecColor(target_normal[Candidate_Stack[node]]-1, i);
          if (con == 0){
            insert[insert_num] = node;
            insert_num++;
            Cand_wrt_nb[j][l] = Cand_wrt_nb[j][counts[j] - 1];
            counts[j]--;
            l--;
            if (insert_num == PARA.KX-t)
              break;
          }
        }
        if (insert_num == PARA.KX-t)
          break;
      }
      int ub1;
      if (insert_num + colors[i].sz < PARA.KX - t)
        ub1 = insert_num + colors[i].sz;
      else
        ub1 = PARA.KX - t;
      if (ub+ub1 > lb){
        int back = kk-1, begin = start;
        if (kk - selected_num - (lb - ub) < Branching_Point){
          for (j = start; j < kk; j++){
            Candidate_Stack2[j] = Candidate_Stack[j];
            NBNN_Stack2[j] = NBNN_Stack[j];
          }
          for (j = 0; j < PARA.KX; j++){
            if (org_counts[j] == 0)  continue;
            for (int l = org_counts[j]-1; l >= 0; l--){
              if (selected[Cand_wrt_nb2[j][l]]){
                Candidate_Stack[back] = Candidate_Stack2[Cand_wrt_nb2[j][l]];
                NBNN_Stack[back] = NBNN_Stack2[Cand_wrt_nb2[j][l]];
                back--;
              }
              else{
                Candidate_Stack[begin] = Candidate_Stack2[Cand_wrt_nb2[j][l]];
                NBNN_Stack[begin] = NBNN_Stack2[Cand_wrt_nb2[j][l]];
                begin++;
              }
            }
          }
          return begin - (lb - ub);
        }
        else{
          return Branching_Point;
        }
      }
      else{
        ub+=ub1;
        for (j = 0; j < colors[i].sz; j++){
          selected[colors[i].index[j]] = 1;
        }
        for (j = 0; j < insert_num; j++){
          selected[insert[j]] = 1;
        }
        selected_num = selected_num + colors[i].sz + insert_num;
      }
    }
  }
  if (ub <= lb){
    return start;
  }  
}

static int cut_by_common_neibor(int start){
  int i,j,neibor, max = 0, *neibors;
  int bnode=Candidate_Stack[CURSOR];
 
  if(CUR_KPX_SIZE>2){
    for(int cn=Candidate_Stack[i=start];cn!=DELIMITER;cn=Candidate_Stack[++i]){
   	  Node_State2.reset(cn);
  	  Node_State.reset(cn);
    }
    for(i=0;i<ptr(Clique_Stack);i++){
      if(Energy_Stack[i]<0){
        Energy_Stack[i]=-Energy_Stack[i];
      }
    } 
    return ptr(Candidate_Stack)-1-(MAX_KPX_SIZE-(CUR_KPX_SIZE));
  }

  neibors = Node_Neibors[bnode];
  for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
    if(Node_State2[neibor])
      Node_State.set(neibor);
  }
  
  for(int cn=Candidate_Stack[i=start];cn!=DELIMITER;cn=Candidate_Stack[++i]){
    CNN[cn]=0;

    neibors = Node_Neibors[cn];
    for (neibor = *neibors; neibor != NONE; neibor = *(++neibors)) {
     if(Node_State[neibor])
       CNN[cn]++;
    }

    int flag= Node_State[cn] ? 0:1;
    int min_NN=MAX_KPX_SIZE - (CUR_KPX_SIZE+1)+1 - CNN[cn];
	 
    if(NBNN_Stack[CURSOR] + NBNN_Stack[i]+min_NN+flag > 2*PARA.KX-2){
      Node_State.reset(cn);
      Candidate_Stack[i]=-cn;
      NB_CANDIDATE--;
    }
  }

  for(int cn=Candidate_Stack[i=start];cn!=DELIMITER;cn=Candidate_Stack[++i]){
      if(cn>0){
	Node_State2.reset(cn);
	Node_State.reset(cn);
      }else{
	Node_State2.reset(-cn);
	Node_State.reset(-cn);
      }
  }  
 
  if(NB_CANDIDATE+CUR_KPX_SIZE>MAX_KPX_SIZE){     
     int j=start,count=0;
     float cutted=0.0;
     for(int cn=Candidate_Stack[i=start];cn!=DELIMITER;cn=Candidate_Stack[++i]){
       if(cn>0){
	 Candidate_Stack[j]=cn;
	 NBNN_Stack[j]=NBNN_Stack[i];
	 count++;
	 j++;
       }else{
	 cutted++;
       }
     }
     Candidate_Stack[j]=DELIMITER;
     ptr(Candidate_Stack)=j+1;
     NBNN_Stack[j]=DELIMITER;
     ptr(NBNN_Stack)=j+1;
     
     assert(count==NB_CANDIDATE);
     
     for(i=0;i<ptr(Clique_Stack);i++){
         if(Energy_Stack[i]<0){
	   Energy_Stack[i]=-Energy_Stack[i];
	 }
     } 
     return ptr(Candidate_Stack)-1-(MAX_KPX_SIZE-(CUR_KPX_SIZE));
  }else{
   for(int i=0;i<ptr(Clique_Stack);i++){
      if(Energy_Stack[i]<0){
	Energy_Stack[i]=-Energy_Stack[i]-1;
      }
   }
    return 0;
  }
}

static void init_for_search() {
	int i, node;
	int neibor, neibor2, *neibors, *neibors2;
	cut_ver = 0;
	cut_inc = 0;
	cut_iset = 0;
	cut_satz = 0;
	total_cut_ver = 0;
	total_cut_inc = 0;
	total_cut_iset = 0;
	total_cut_satz = 0;

	Branches_Nodes[0] = 0;
	Branches_Nodes[1] = 0;
	Branches_Nodes[2] = 0;
	Branches_Nodes[3] = 0;
	Branches_Nodes[4] = 0;
	Branches_Nodes[5] = 0;

	Last_Idx = NB_NODE;
	NB_BACK_CLIQUE = 0;
	MAX_KPX_SIZE = 0;
	ptr(Clique_Stack) = 0;
	ptr(Energy_Stack) =0;
	ptr(Cursor_Stack) = 0;
	Rollback_Point = 0;
	Reasoning_Point=0;


	push(NB_NODE - INIT_KPX_SIZE - 1, Cursor_Stack);
	MAX_KPX_SIZE = INIT_KPX_SIZE;

	//	assert(Candidate_Stack[ptr(Candidate_Stack)- 2]==1);
	assert(ptr(NBNN_Stack)==ptr(Candidate_Stack));
	
	for (i = 0; i < ptr(Candidate_Stack) - 1; i++) {
		node = Candidate_Stack[i];
		Vertex_UB[i] = Node_Degree[node] + PARA.KX;
		NBNN_Stack[i]=0;
		
	
	}
	
	NBNN_Stack[NB_NODE]=DELIMITER;
	ptr(NBNN_Stack)=ptr(Candidate_Stack);
}

static void allocate_memory() {
	int i;

	Second_Name = (int *) malloc((MAX_VERTEX_NO + 1) * sizeof(int));

	CNN=(int *)malloc((MAX_VERTEX_NO+1)*sizeof(int));
}

static void search_maxclique(int cutoff, int silent) {
	int bnode;
	init_for_search();
	BRANCHING_COUNT = 0;
 
	if (silent==0) {
		printf(
				"C  ---------------------------------------\n");
		printf(
				"C  Size|   Index|   NB_Branches|   Time(s)\n");
	}	
	while (CURSOR> 0) {
    if(BRANCHING_COUNT % 1000 == 0 && get_utime() > 7200){
	  //if(CUT_OFF>0 && get_utime()> CUT_OFF){
            TIME_OUT=TRUE;
            break;
	  }
	  bnode=Candidate_Stack[--CURSOR];
	  #ifdef ISET
	  if(Reasoning_Point && bnode>0)
	    continue;
	  #endif
	  
	  if(bnode==DELIMITER) {
	    ptr(NBNN_Stack)=ptr(Candidate_Stack)=CURSOR+1;
	    ptr(Cursor_Stack)--;
	    ptr(Clique_Stack)--;
	    ptr(Energy_Stack)--;
	    // assert(Candidate_Stack[CURSOR]==Clique_Stack[ptr(Clique_Stack)]);
	    int pop_node=Clique_Stack[ptr(Clique_Stack)];

	    // check_solution1();
	    for(int i=0;i<ptr(Clique_Stack);i++){
             if(is_adjacent(Clique_Stack[i],pop_node)==FALSE){
	       Energy_Stack[i]--;
             }
	    }	  
	  //check_solution0();
	  
	  //Vertex_UB[CURSOR]=MAX_KPX_SIZE-CUR_KPX_SIZE;
	  if(pop_node==Reasoning_Point){
	    Reasoning_Point=0;
	  }	  
	} else {
	    
	  /* if(bnode<0) {
	    bnode=-bnode;
	    Candidate_Stack[CURSOR]=-Candidate_Stack[CURSOR];
	  }
	    */
	  if(MAX_KPX_SIZE==CUR_KPX_SIZE) {
	    store_maximum_clique(bnode,silent);
	  }
	  //else if(0 && Vertex_UB[CURSOR] <= MAX_KPX_SIZE - CUR_KPX_SIZE) {
	  //  cut_ver++;
	  // }
	  else {
	    BRANCHING_COUNT++;
      
      //std::cout << trials << " " << success1 << " " << success2 << endl;   
      
	    Rollback_Point=ptr(Candidate_Stack);
	    //push clique stack
	    //if(Reasoning_Point==0)
	    push(bnode, Clique_Stack);
	    
	    push(NBNN_Stack[CURSOR],Energy_Stack);

	    #ifdef COMM
	      if((Branching_Point=produce_subgraph0())==0
		 || (Branching_Point=cut_by_common_neibor(Rollback_Point))==0)
	    #elif  defined(PART)
	       if((Branching_Point=produce_subgraph0())==0
		    || (Branching_Point=cut_by_iteration_partition())==0
		   )
            #elif defined(ALL)
		  if((Branching_Point=produce_subgraph0())==0
		    || (Branching_Point=cut_by_common_neibor(Rollback_Point))==0
        || (Branching_Point=cut_by_iteration_partition())==0
        || (Branching_Point=cut_by_zjz(Rollback_Point))==0
		   )
	    #else
		if((Branching_Point=produce_subgraph0())==0)
	    #endif
	    {
	      ptr(NBNN_Stack)=ptr(Candidate_Stack)=Rollback_Point;
	      ptr(Clique_Stack)--;
	      ptr(Energy_Stack)--;

	      continue;
	    }
	  
	    push(Branching_Point,Cursor_Stack);
	    //check_solution2();
	  }
	}
	}
	
      SEARCH_TIME = get_utime();
	if (silent==0) {
	  /*printf(
				"C  -----------------------------------------------------------------------------\n");
		printf("C %4d |%7d |%8d %10d %10d %10d|%14lld %8.2lf\n", MAX_KPX_SIZE, CURSOR,cut_ver,cut_inc, cut_iset, cut_satz,BRANCHING_COUNT,SEARCH_TIME);
		total_cut_ver += cut_ver;
		total_cut_inc += cut_inc;
		total_cut_iset += cut_iset;
		total_cut_satz += cut_satz;*/
		printf(
				"C  ---------------------------------------\n");
		printf("C %4d |%7d |%14lld| %8.2lf\n", MAX_KPX_SIZE, CURSOR,BRANCHING_COUNT,SEARCH_TIME);
	}
}

static int * Adj_List;
#define New_Name Node_Degree


static void free_block() {
	int i = 0;
	for (i = 0; i < BLOCK_COUNT; i++)
		free(BLOCK_LIST[i]);
}

static void reduce_instance_with_unsupport_property(){
  int level=0;
  int  p1,p2,p3,i,node, *neibors1,*neibors2;

  for(int i=1;i<=NB_NODE;i++){
    assert(Node_State[i]==0);
    assert(Node_State2[i]==0);
    assert(Candidate_Stack[i-1]>0);
    assert(Candidate_Stack[NB_NODE-i]==i);
  }
  printf("R Reducing at level%3d",level);
  fflush(stdout);
  do{
    printf("\b\b\b%3d",++level);fflush(stdout);
    for(p1= Candidate_Stack[i=0];p1!=DELIMITER; p1= Candidate_Stack[++i]){
      if(p1<=0)continue;
      neibors1 = Node_Neibors[p1];
      for (p2 = *neibors1; p2 != p1; p2 = *(neibors1+=2)) {
       *(neibors1+1)=0;
      }
    }
   //list all triangles <p1,p2,p3>,computer common neibors for an edge <u,v>
   for(p1= Candidate_Stack[i=0];p1!=DELIMITER; p1= Candidate_Stack[++i]){
     if(p1<=0)continue;
     assert(p1== Candidate_Stack[NB_NODE-p1]);
     
     neibors1 = Node_Neibors[p1];
     for (p2 = *neibors1; p2<p1; p2 = *(neibors1+=2)) {
       if(p2>0){
	 if(Candidate_Stack[NB_NODE-p2]<0)
	   *(neibors1)=-p2;
	 else
	   Node_State.set(p2);
       }else if((-p2)>p1){
	 break;
       }
     }
     
     neibors1 = Node_Neibors[p1];
     for (p2 = *neibors1; (p2<p1) && p1+p2>0; p2 = *(neibors1+=2)) {
     
	if(p2<0)continue;      

       assert(Node_State[p2]);
       assert(Node_Degree[p2]+PARA.KX > INIT_KPX_SIZE);

       neibors2 = Node_Neibors[p2];
       for (p3= *neibors2; p3<p2; p3 = *(neibors2+=2)) {
         if(p3>0 && Node_State[p3]){
	    Node_State2.set(p3);
	    *(neibors1+1)=*(neibors1+1)+1;
	    *(neibors2+1)=*(neibors2+1)+1;
	 }else if ((-p3)>p2){
	   break;
	 }
       }
       neibors2 = Node_Neibors[p1];
       for (p3 = *neibors2; p3 < p2; p3 = *(neibors2+=2)) {
         if(p3>0 && Node_State2[p3]){
	   *(neibors2+1)=*(neibors2+1)+1;
	   Node_State2.reset(p3);
	 }else if((-p3)>p2){
	   break;
	 }
       }
     }
     
     neibors1 = Node_Neibors[p1];
     for (p2 = *neibors1; p2<p1; p2 = *(neibors1+=2)) {
       if(p2>0){
	 Node_State.reset(p2);
       }else if((-p2)>p1){
	 break;
       }
     }
   }
   

   ptr(Extra_Node_Stack)=0;
   //check all edges <p1,p2>, break <p1,p2> if comm(p1,p2)+2k<=LB
   //push vertices that can be removed
   for(p1= Candidate_Stack[i=0];p1!=DELIMITER; p1= Candidate_Stack[++i]){
     if(p1<=0)continue;
     
     neibors1 = Node_Neibors[p1];
     
     for (p2 = *neibors1; (p2<p1) && (p1+p2>0); p2 = *(neibors1+=2)) {
     
       if(p2>0 && *(neibors1+1)+2*PARA.KX<=INIT_KPX_SIZE){
	 Node_Degree[p1]--;
	 *neibors1=-p2;
	 
	 neibors2 = Node_Neibors[p2];
         for (p3 = *neibors2; p3 != p2; p3 = *(neibors2+=2)) {
	   if(p3==p1){
	     *neibors2=-p1;
	     Node_Degree[p2]--;
	     break;
	   } 
	 }
	 assert(p3==p1);
       }
     }
     if(Node_Degree[p1]+PARA.KX<=INIT_KPX_SIZE){
       assert(p1>0);
       push(p1,Extra_Node_Stack);
     }
   }
   push(DELIMITER,Extra_Node_Stack);

   //removed vertices recursively
   for(int p1=Extra_Node_Stack[i=0];p1!=DELIMITER;p1=Extra_Node_Stack[++i]){  
     assert(p1>0);
     assert(Node_Degree[p1]<=INIT_KPX_SIZE-PARA.KX);
     assert(Candidate_Stack[NB_NODE-p1]==p1);
       
     Candidate_Stack[NB_NODE-p1]=-p1;
     neibors1 = Node_Neibors[p1];
     for (int p2 = *neibors1; p2 != p1; p2 = *(neibors1+=2)) {
       if(p2>0 && Node_Degree[p2]+PARA.KX>INIT_KPX_SIZE){
	 Node_Degree[p2]--;
	 if(Node_Degree[p2]+PARA.KX<=INIT_KPX_SIZE){
	   assert(p2>0);
	   Extra_Node_Stack[ptr(Extra_Node_Stack)-1]=p2;
	   push(DELIMITER,Extra_Node_Stack);
	 }
       }
     }
   }
 
  }while(ptr(Extra_Node_Stack)>1);

  printf("\n");
}


static int reduce_instance2(){
  int i=0,j=0,nb_edge=0;
  int  node, *neibors, *neibors2, *addr;
  MAX_VERTEX_NO=0;
  for(int p1= Candidate_Stack[i=0];p1!=DELIMITER; p1= Candidate_Stack[++i]){
    if(p1>0){
       Candidate_Stack[j++] = p1;
       Node_State.set(p1);
       Node_Degree[p1]=0;
      
    }
  }
  NB_NODE = j;
  
  if(NB_NODE<=INIT_KPX_SIZE){
    printf("I prove the optimal in reduction phase!\n");
    return TRUE;
  }
    
  NBNN_Stack[j]=Candidate_Stack[j] = DELIMITER;
  ptr(NBNN_Stack)=ptr(Candidate_Stack) = j + 1;
  
  max_node_index = j-1;
  
  NB_EDGE = 0;
  neibors2=Adj_List;
  for(int p1= Candidate_Stack[i=0];p1!=DELIMITER; p1= Candidate_Stack[++i]){
    neibors = Node_Neibors[p1];
    //neibors2 = neibors;
    //std::cout<<p1<<": ";
    for (node = *neibors; node != p1; node = *(neibors+=2)) {
      //if(node<0)node=-node;      
       if(node>0 && Node_State[node]) {
       //std::cout<<node<<" ";
	 Node_Degree[p1]++;
	 *neibors2 = node;
	 neibors2++;
	 NB_EDGE++;
       }
    }
    //std::cout<<endl;
    (*neibors2) = NONE;
    neibors2++;
  }
  Node_Neibors[Candidate_Stack[0]]=Adj_List;
  for(int p0=Candidate_Stack[0],p1= Candidate_Stack[i=1];p1!=DELIMITER;p0=p1,p1= Candidate_Stack[++i]){
    Node_Neibors[p1]=Node_Neibors[p0]+ Node_Degree[p0]+1;
    Node_State.reset(p1);
  }

  NB_EDGE=NB_EDGE/2;
 
  MAX_VERTEX_NO=Candidate_Stack[0];
  printf("I the second level reduced graph #node %d #edge %d #density %9.8f\n", j,
	 NB_EDGE, ((float)2* NB_EDGE  / NB_NODE / (NB_NODE-1)));

  return FALSE;
}


static int reduce_instance_with_degree() {

  int flag=1;
  int i=0,nb=0, node, *neibors, *neibors2, *addr;
  for (i = 0,nb=0; i < NB_NODE; i++) {
    node = Candidate_Stack[i];
    if (flag && Node_Degree[node]+PARA.KX <= INIT_KPX_SIZE) {
       Node_State[node] = PASSIVE;
    } else {
       flag=0;
       Candidate_Stack[nb++] = node;
       Node_State[node] = ACTIVE;
    }
  }
  NB_NODE = nb;

  if(NB_NODE<=INIT_KPX_SIZE){
    printf("I find the optimal solution in level-1 reduction.\n");
    return TRUE;
  }    
  
  N0_1 = NB_NODE;
  NBNN_Stack[nb]=Candidate_Stack[nb] = DELIMITER;
  ptr(NBNN_Stack)=ptr(Candidate_Stack) = nb + 1;

  Old_Name = (int *) malloc((NB_NODE + 1) * sizeof(int));
  for (i = 0; i < NB_NODE; i++) {
    Old_Name[NB_NODE - i] = Candidate_Stack[i];
    New_Name[Candidate_Stack[i]] = NB_NODE - i;
    Candidate_Stack[i] = NB_NODE - i;
  }
 
	NB_EDGE = 0;
	for (i = NB_NODE; i > 0; i--) {
		neibors = Node_Neibors[Old_Name[i]];
		neibors2 = neibors;
		nb = 0;
		for (node = *neibors; node != NONE; node = *(++neibors)) {
		  if (Node_State[node]==ACTIVE) {
		    (*neibors2) = New_Name[node];
		    neibors2++;
		    nb++;
		  }
		}
		(*neibors2) = NONE;
		NB_EDGE += nb;
		qsort(Node_Neibors[Old_Name[i]], nb, sizeof(int), int_cmp_asc);
		assert(nb+PARA.KX > INIT_KPX_SIZE);
	}
	NB_EDGE=NB_EDGE/2;
	
	Adj_List = (int *) malloc((4*NB_EDGE + NB_NODE) * sizeof(int));
	addr = Adj_List;

	if (Adj_List == NULL ) {
		printf("can't allocate enough memory for Adj_List!\n");
		exit(1);
	}
	for (MAX_VERTEX_NO = 0,i = NB_NODE; i > 0; i--) {
		Node_Degree[i] = 0;
		Node_State.reset(i);
		Node_State2.reset(i);
		neibors = Node_Neibors[Old_Name[i]];
		for (node = *neibors; node != NONE; node = *(++neibors)) {
			*(addr++) = node;
			*(addr++) = 0;
			Node_Degree[i]++;
		}
		*(addr++) = i;
		if (Node_Degree[i] > MAX_VERTEX_NO)
			MAX_VERTEX_NO = Node_Degree[i];
		assert(Node_Degree[i]+PARA.KX> INIT_KPX_SIZE);
	}
	free_block();
	Node_Neibors[NB_NODE] = Adj_List;
	for (i = NB_NODE - 1; i > 0; i--) {
	  Node_Neibors[i] = Node_Neibors[i + 1] + 2*Node_Degree[i + 1] + 1;
	}
	
	D1 = ((float) NB_EDGE*2  / NB_NODE / (NB_NODE - 1));
	printf("I the L1-Reduced graph #node %d #edge %d #density %9.8f\n", NB_NODE,
	       NB_EDGE, ((float) NB_EDGE*2  / NB_NODE / (NB_NODE - 1)));
	//	printf("I the largest subgraph is %d\n", MAX_VERTEX_NO);
	return FALSE;
}

static int initialize() {
  int r = sort_by_degeneracy_ordering();
  if (r == FALSE) {
    r=reduce_instance_with_degree();
    if(r==FALSE){
      reduce_instance_with_unsupport_property();
      r=reduce_instance2();
    }
  
  }
  INIT_TIME = get_utime() - READ_TIME;

  if(r==TRUE){
    SEARCH_TIME=READ_TIME+INIT_TIME;
    printf("S ");
    for(int i=0;i<MAX_KPX_SIZE;i++){
      printf("%d ", MaxCLQ_Stack[i]);
    }
    printf("\n");
  }
 printf("I the initial time is %4.2lf \n", INIT_TIME);
 return r;
}

static char * getInstanceName(char *s) {
	if (strrchr(s, '/') == NULL )
		return s;
	else
		return strrchr(s, '/') + 1;
}

void parse_parameters(int argc,char* argv[]){
  PARA.ORDER =-1;
  PARA.FORMAT=1;
  PARA.START_MAXSAT_THD=15;
  PARA.CUT_OFF=0;
  PARA.TIME_OUT=0;
  for (int i = 2; i < argc; i++) {
      if (strcmp(argv[i],"-x")==0){
	sscanf(argv[++i], "%d", &PARA.KX);
      }else if (strcmp(argv[i], "-o") == 0){
	sscanf(argv[++i], "%d", &PARA.ORDER);
      }else if (strcmp(argv[i], "-f") == 0){
	sscanf(argv[++i], "%d", &PARA.FORMAT);
      } else if (strcmp(argv[i], "-i") == 0) {
	sscanf(argv[++i], "%d", &PARA.START_MAXSAT_THD);
      }else if (strcmp(argv[i], "-c") == 0) {
	sscanf(argv[++i], "%d", &PARA.CUT_OFF);
      }else if(strcmp(argv[i],"-m")==0){
	sscanf(argv[++i], "%f", &BMTHD);
      }else if(strcmp(argv[i],"-ms")==0){
	sscanf(argv[++i],"%d",&MAX_MATRIX_SIZE);
      }
  }
  printf("# Solving %d-plex in %s\n\n",PARA.KX,argv[1]);
}
 
static void check_and_print_solution(){
  int count=0,count1=0,node1;
  if(MAX_KPX_SIZE>INIT_KPX_SIZE){
  for(int i=0; i<MAX_KPX_SIZE ; i++){
    count=0;count1=0;
    node1=MaxCLQ_Stack[i];
    for(int j=0;j<MAX_KPX_SIZE;j++){
      if(MaxCLQ_Stack[j]==node1)
	count1++;
      else if(is_adjacent(node1,MaxCLQ_Stack[j])==FALSE)
	count++;
    }
    if(count>PARA.KX-1)
      std::cout<<"count "<<count<<" "<<PARA.KX-1<<endl;
    assert(count1==1);
    assert(count<=PARA.KX-1);
    //assert(count==Energy_Stack[i]);
  }
  }
  printf("S ");
  for(int i=0;i<MAX_KPX_SIZE;i++){
    if(MAX_KPX_SIZE>INIT_KPX_SIZE){
     printf("%d ",Old_Name[MaxCLQ_Stack[i]]);
    }else{
     printf("%d ",MaxCLQ_Stack[i]);
    }
  }
  printf("\n");
}
int main(int argc, char *argv[]) {
  parse_parameters(argc,argv);
  if (build_simple_graph_instance(argv[1])) {
    if (initialize() == FALSE) {
      //if (NB_NODE >= 500000){
      //  std::cout<<"Out of Memory!"<<endl;
      //  return 0;
      //}
      colors = new ColorType[NB_NODE+1];
      for (int i = 0; i < NB_NODE + 1; i++) {
        colors[i].bitcolor = MBitSet64(NB_NODE);
        colors[i].vertices = new unsigned int[NB_NODE];
        colors[i].index = new unsigned int[NB_NODE];
        colors[i].sz = 0;			
      }	
      
      Cand_wrt_nb = new int* [PARA.KX];
      Cand_wrt_nb2 = new int* [PARA.KX];
      for (int i = 0; i < PARA.KX; i++){
        Cand_wrt_nb[i] = new int [NB_NODE + 1];
        Cand_wrt_nb2[i] = new int [NB_NODE + 1];
      }
      
      Candidate_Stack2 = new int [MAX_NODE * 2];
      NBNN_Stack2 = new int [MAX_NODE * 2];
      selected = new int [MAX_NODE * 2];
      
      target_normal = new int[Candidate_Stack[0]+1];
      target_abnormal = new int[NB_NODE+1];
      int normal_node = 1;
      for(int i = max_node_index; i >= 0; i--){
        int temp_n = Candidate_Stack[i];
        target_normal[temp_n] = normal_node;
        target_abnormal[normal_node] = temp_n;
        normal_node++;
      }
      
      kernalG.nbvtx = NB_NODE; kernalG.nbedges = 2*NB_EDGE;
      kernalG.pstart = new int[NB_NODE+1];
      kernalG.edges = new unsigned int[2*NB_EDGE+2];
      kernalG.pstart[0] = 0;
      for (int i = 0; i < NB_NODE; i++)
        kernalG.pstart[i+1] = kernalG.pstart[i] + Node_Degree[target_abnormal[i+1]];
      int edge_num = 0;
      for (int i = 1; i <= NB_NODE; i++){
        int neibor, *neibors = Node_Neibors[target_abnormal[i]];
        for (neibor = *neibors; neibor!=NONE; neibor = *(++neibors)){
          kernalG.edges[edge_num++] = target_normal[neibor]-1;
        }
      }
      bg = new MBitGraph(kernalG);
      //assert(edge_num == NB_EDGE);
      
      allocate_memory();
      search_maxclique(0, 0);
      check_and_print_solution();
      
      delete[] target_normal;
      delete[] target_abnormal;
      for (int i = 0; i < PARA.KX; i++){
        delete[] Cand_wrt_nb[i];
        delete[] Cand_wrt_nb2[i];
      }
      delete[] Cand_wrt_nb;
      delete[] Cand_wrt_nb2;
      delete[] Candidate_Stack2;
      delete[] NBNN_Stack2;
      delete[] selected;
    }
   }
    
  printf(
	 ">>%s |V| %d |E| %d KG+1 %d MaxKPX %d InitKPX %d Tree %lld Read_Time %4.2lf Init_Time %4.2lf Search_Time %4.2lf Total %4.2lf \\\\\n",
	 getInstanceName(argv[1]), NB_NODE_O, NB_EDGE_O, K_CORE_G + 1,
	 MAX_KPX_SIZE, HEUR_KPX_SIZE, BRANCHING_COUNT, READ_TIME, INIT_TIME,
	 SEARCH_TIME - READ_TIME - INIT_TIME, SEARCH_TIME);
	
 if (TIME_OUT != TRUE)  OPT = 1;
 
  return 0;
}

