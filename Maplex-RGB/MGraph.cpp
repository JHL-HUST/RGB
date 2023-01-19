#include "MGraph.h"
#include "LinearHeap.h"
#include <algorithm>

#ifdef NDEBUG
#undef NDEBUG
#include <assert.h>
#endif
MCsrGraph::MCsrGraph(const MBitGraph& bitg){
        nbvtx = bitg.nbvtx;
        nbedges = bitg.nbedges;
        pstart =new int[nbvtx+1];
        edges = new ui[nbedges];
        int cnt = 0;
        for (ui i = 0; i < nbvtx; i++){
            pstart[i] = cnt;
            for (ui j = 0; j < nbvtx; j++){
                if ((bitg.rows[i])->test(j)){
                    edges[cnt++] = j; 
                }
            }
        }
        pstart[nbvtx] = cnt;
        assert(cnt == nbedges);
}


//grpah algorithm: core decomposition
int coreDecomposition(const MCsrGraph &g, int *core, ui* seq, int* pos){
    assert(core!= nullptr && seq!= nullptr && pos!= nullptr);

    int *degree = new int[g.nbvtx];	
	char *isout = new char[g.nbvtx];
	for (ui i = 0; i < g.nbvtx; i++) {		
		degree[i] = g.degree(i);		
        seq[i] = i;
		isout[i] = 0;
	}

	int max_core = 0;
	ListLinearHeap *linear_heap = new ListLinearHeap(g.nbvtx, g.nbvtx);
	linear_heap->init(g.nbvtx, g.nbvtx - 1, seq, (ui*)degree);	
	for (ui i = 0; i < g.nbvtx; i++) {
		ui u, key;
		linear_heap->pop_min(u, key);
		if (key > max_core)
			max_core = key;		
		seq[i] = u;
		core[u] = max_core;
        pos[u] = i;
		isout[u] = 1;
		for (ui j = g.pstart[u]; j < g.pstart[u + 1]; j++)
			if (!isout[g.edges[j]])
				linear_heap->decrement(g.edges[j]);		
	}	
    delete[] degree;
    delete[] isout;
    delete linear_heap;
    return max_core;
}

//Prerequisite: lst1 and lst2 are sorted incrementally.
int countIntersect(ui *lst1, int sz1, ui *lst2, int sz2){
	if (sz1 ==0 || sz2 == 0) return 0;
	int p1=0, p2=0;
	int cnt = 0;
	while (p1 < sz1 && p2 <sz2){
		if (lst1[p1] == lst2[p2]){
			p1++;p2++; cnt++;
		}else if(lst1[p1] < lst2[p2])
			p1++;
		else p2++;
	}
	return cnt;
}

void countingTriangles(const MCsrGraph &g, int *pos, int *triangles){
	 //triangle counting
	assert( pos != nullptr  && triangles != nullptr);
	//debug...
	//memset(triangles, -1, sizeof(int) * g.nbedges);
	//counting triangles
	for (ui u = 0; u < g.nbvtx; u++){
		for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
			ui neiu = g.edges[j];
			assert(pos[u] != pos[neiu]);
			if (pos[u] < pos[neiu]){
				triangles[j] = countIntersect(g.edges+g.pstart[u], g.degree(u), g.edges+g.pstart[neiu], g.degree(neiu));
			}
		}
	}
    for (ui u = 0; u < g.nbvtx; u++){
        for (int j = g.pstart[u]; j < g.pstart[u+1]; j++){
            ui neiu = g.edges[j];
            if (pos[u] >= pos[neiu]){
		        ui* it = std::find(g.edges + g.pstart[neiu], g.edges + g.pstart[neiu+1], u);
                assert(it != g.edges + g.pstart[neiu+1]);
				int tpos = std::distance(g.edges, it);
				//assert(triangles[tpos] != -1);                
				triangles[j] = triangles[tpos];
            }
        }
    }  
}
ui* bsearch_with_index(ui* first, ui* last, ui data) {
    auto it = std::lower_bound(first, last, data);
    if (it == last || *it != data) {
        return  last;
    } else {        
        return it;
    }   
}

void testTriCounting(){
     MCsrGraph cg;
    cg.fromBinaryFile("realinstances\\binfmt\\bio-celegans.bin");
    int *core= new int[cg.nbvtx];
    ui *seq = new ui[cg.nbvtx];
    int *pos = new int[cg.nbvtx];
    int maxc = coreDecomposition(cg, core, seq, pos);

    int *cnt = new int[cg.nbedges];
    countingTriangles(cg, pos,cnt);
    /*for (ui u = 0; u < cg.nbvtx; u++){
        for (int j = cg.pstart[u]; j < cg.pstart[u+1]; j++){
            printf("%d %d: %d\n", u, cg.edges[j], cnt[j]);
        }
    }*/

    //verification
    for (ui u = 0; u < cg.nbvtx; u++){
        std::set<ui> su(cg.edges + cg.pstart[u], cg.edges + cg.pstart[u+1]);
        /*printf("vertex %d, pos: %d neis:", u, pos[u]);
        for(int j = cg.pstart[u]; j < cg.pstart[u+1]; j++){
            printf("%d ", cg.edges[j]);
        }
        printf("\n");*/
        for(int j = cg.pstart[u]; j < cg.pstart[u+1]; j++){
            ui neiu = cg.edges[j];            
            std::set<ui> sj(cg.edges + cg.pstart[neiu], cg.edges+cg.pstart[neiu+1]);
            /*printf("vertex %d, pos %d,  neis:", neiu, pos[neiu]);
            for (ui k = cg.pstart[neiu]; k < cg.pstart[neiu+1]; k++){
                printf("%d ", cg.edges[k]);
            }
            printf("\n");*/
            std::vector<ui> v(std::max(cg.pstart[u+1]-cg.pstart[u], cg.pstart[neiu+1] - cg.pstart[neiu]));
            std::vector<ui>::iterator it = std::set_intersection(su.begin(), su.end(), sj.begin(), sj.end(), v.begin());
            v.resize(it- v.begin());
            assert(v.size() == cnt[j]);
            //printf("Intersection %d-%d:", u, neiu);
            //for (auto x:v) printf("%d ", x);
            //printf("\n%d - %d\n",v.size(), cnt[j]);
            /*if(v.size()  != cnt[j]){
                printf("pause\n");
                exit(0);
            }*/
        }
    }
    printf("PASS\n");
    
}
void testCoreDecomp(){
    MCsrGraph cg;
    cg.fromBinaryFile("realinstances\\bio-celegans.bin");
    int *core= new int[cg.nbvtx];
    ui *seq = new ui[cg.nbvtx];
    int *pos = new int[cg.nbvtx];
    int maxc = coreDecomposition(cg, core, seq, pos);
    for (int i = 0; i < cg.nbvtx; i++)
        printf("%d: %d %d\n", i, seq[i], core[seq[i]]);
}

void testConstruct(){
    MCsrGraph cg;
    cg.fromBinaryFile("realinstances\\binfmt\\bio-celegans.bin");
    MBitGraph bg(cg);
    for (int i = 0; i < cg.nbvtx; i++){
        for (int j = cg.pstart[i]; j < cg.pstart[i+1]; j++)
            if (!(bg.rows[i])->test(cg.edges[j])){
                printf("wrong\n");
            }
    }
    MCsrGraph mcg(bg);
    for (int i = 0; i < mcg.nbvtx; i++){
        for (int j = mcg.pstart[i]; j < mcg.pstart[i+1]; j++)
            if (mcg.edges[j] != cg.edges[j])
                printf("wrong\n");
    }
}

int __main__(int argc, char **argv){
   // testCoreDecomp();
   //testConstruct();
   testTriCounting();
    return 0;
}