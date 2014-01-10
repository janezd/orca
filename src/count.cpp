/*
 Orca (Orbit Counting Algorithm) - A combinatorial approach to graphlet counting
 Copyright (C) 2013  Tomaz Hocevar <tomaz.hocevar@fri.uni-lj.si>
 
 This program is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or
 (at your option) any later version.
 
 This program is distributed in the hope that it will be useful,
 but WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 GNU General Public License for more details.
 
 You should have received a copy of the GNU General Public License
 along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#include <cstdlib>
#include <cstring>
#include <cassert>
#include <ctime>
#include <iostream>
#include <fstream>
#include <set>
#include <unordered_map>
#include <algorithm>

#include "Rinternals.h"
#include <Rdefines.h>
#include <Rmath.h>
#include <R_ext/Rdynload.h>

using namespace std;


typedef long long int64;
typedef pair<int,int> PII;

struct PAIR {
	int a, b;
    inline PAIR(int const &aa, int const &bb) {
        if (aa < bb) {
            a = aa; b = bb;
        }
        else {
            a = bb; b = aa;
        }
    }
};

bool operator <(const PAIR &x, const PAIR &y) {
	if (x.a == y.a)
        return x.b < y.b;
	else
        return x.a < y.a;
}

bool operator ==(const PAIR &x, const PAIR &y) {
	return x.a == y.a && x.b == y.b;
}

struct hash_PAIR {
	size_t operator()(const PAIR &x) const {
		return (x.a << 8) ^ (x.b << 0);
	}
};

struct TRIPLE {
	int a, b, c;
	TRIPLE(int a0, int b0, int c0)
    : a(a0), b(b0), c(c0) {
		if (a > b) swap(a, b);
		if (b > c) swap(b, c);
		if (a > b) swap(a, b);
	}
};

bool operator <(const TRIPLE &x, const TRIPLE &y) {
	if (x.a == y.a) {
		if (x.b == y.b)
            return x.c < y.c;
		else
            return x.b < y.b;
	} else
        return x.a < y.a;
}

bool operator ==(const TRIPLE &x, const TRIPLE &y) {
	return x.a == y.a && x.b == y.b && x.c == y.c;
}

struct hash_TRIPLE {
	size_t operator ()(const TRIPLE &x) const {
		return (x.a << 16) ^ (x.b << 8) ^ (x.c << 0);
	}
};

#define ORBIT(node,orb) (orbits[(node) + (orb) * n])

#define adj_chunk (8 * sizeof(int))

struct GraphData {
    int n_nodes, n_edges;
    int d_max;
    PAIR *edges;
    PAIR const *const edges_end;
    int *deg;  // node degrees
    int **adj; // adj[x] - adjacency list of node x
    PII **inc; // inc[x] - incidence list of node x: (y, edge id)
    int *adj_matrix; // compressed adjacency matrix; initialized iff smaller than 100 MB
    
    GraphData(PAIR *edges, int *dim_edges);
    
    
    inline bool adjacent_list(int const &x, int const &y) const
    {
        return binary_search(adj[x], adj[x] + deg[x], y);
    }
    
    inline bool adjacent_matrix(int const &x, int const &y) const
    {
        return adj_matrix[(x * n_nodes + y) / adj_chunk] & (1 << ((x * n_nodes + y) % adj_chunk));
    }
    
    inline bool adjacent(int const &x, int const &y) const {
        return adj_matrix ? adjacent_matrix(x, y) : adjacent_list(x, y);
    }
};


GraphData::GraphData(PAIR *p_edges, int *dim_edges)
: n_nodes(0), n_edges(dim_edges[1]), d_max(0),
  edges(p_edges), edges_end(edges + dim_edges[1]),
  deg(NULL), inc(NULL), adj_matrix(NULL)
{
    if (dim_edges[0] != 2) {
        throw "Incorrect size of edges matrix";
    }
    /* TODO Fix
    if (int(set<PAIR>(edges, edges_end).size()) ! = n_edges) {
        throw("Input file contains duplicate undirected edges.");
    }
    */
    PAIR *edge;
    int i;
    for(edge = edges; edge != edges_end; edge++) {
        edge->a--;
        edge->b--;
        if (edge->a > edge->b) {
            swap(edge->a, edge->b);
        }
        if (edge->a < 0) {
            throw "Node ids should be positive";
        }
        if (edge->b > n_nodes) {
            n_nodes = edge->b;
        }
    }
    n_nodes++; // assume zero-based indices

    deg = (int *)S_alloc(n_nodes, sizeof(int));
    for(edge = edges; edge != edges_end; edge++) {
        deg[edge->a]++;
        deg[edge->b]++;
    }
    for(i = 0; i < n_nodes; i++) {
        if (deg[i] > d_max) {
            d_max = deg[i];
        }
    }

    // set up adjacency matrix if it's smaller than 100MB
    if ((int64)n_nodes * n_nodes < 100LL * 1024 * 1024 * 8) {
        adj_matrix = (int *)S_alloc((n_nodes * n_nodes) / adj_chunk + 1, sizeof(int));
        for (edge = edges; edge != edges_end; edge++) {
            int &a = edge->a, &b = edge->b;
            adj_matrix[(a * n_nodes + b) / adj_chunk] |= (1 << ((a * n_nodes + b) % adj_chunk));
            adj_matrix[(b * n_nodes + a) / adj_chunk] |= (1 << ((b * n_nodes + a) % adj_chunk));
        }
    }
    // set up adjacency, incidence lists
    adj = (int **)R_alloc(n_nodes, sizeof(int *));
    inc = (PII **)R_alloc(n_nodes, sizeof(PII *));
    for (int i = 0;i < n_nodes; i++) {
        adj[i] = (int *)R_alloc(deg[i], sizeof(int));
        inc[i] = (PII *)R_alloc(deg[i], sizeof(PII));
    }
    int *d = (int *)S_alloc(n_nodes, sizeof(int));
    for (i = 0; i < n_edges; i++) {
        int &a = edges[i].a, &b = edges[i].b;
        adj[a][d[a]] = b;
        adj[b][d[b]] = a;
        inc[a][d[a]] = PII(b, i);
        inc[b][d[b]] = PII(a, i);
        d[a]++;
        d[b]++;
    }

    for (int i = 0; i < n_nodes; i++) {
        sort(adj[i], adj[i] + deg[i]);
        sort(inc[i], inc[i] + deg[i]);
    }
}




/** count graphlets on 4 nodes */

extern "C" void count4(PAIR *p_edges, int *dim_edges, int *orbits)
{
    try {
        int nn;
        GraphData data(p_edges, dim_edges);
        
        int const &n = data.n_nodes;
        int const &m = data.n_edges;
        PAIR const *const edges = data.edges;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;
        
        // precompute triangles that span over edges
        int *tri = (int *)S_alloc(m, sizeof(int));
        for (int i = 0; i < m; i++) {
            int x = edges[i].a, y = edges[i].b;
            for (int xi = 0,yi = 0; xi < deg[x] && yi < deg[y]; ) {
                if (adj[x][xi] == adj[y][yi]) {
                    tri[i]++;
                    xi++;
                    yi++; }
                else if (adj[x][xi] < adj[y][yi]) {
                    xi++;
                }
                else {
                    yi++;
                }
            }
        }
        
        int64 *C4 = (int64 *)S_alloc(data.n_nodes, sizeof(int64));
        int *neigh = (int *)S_alloc(n, sizeof(int));
        
        for (int x = 0; x < data.n_nodes; x++) {
            for (int nx = 0; nx < data.deg[x]; nx++) {
                int y = adj[x][nx];
                if (y >= x)
                    break;
                nn = 0;
                for (int ny = 0; ny < data.deg[y]; ny++) {
                    int z = adj[y][ny];
                    if (z >= y)
                        break;
                    if (!data.adjacent(x, z))
                        continue;
                    neigh[nn++] = z;
                }
                for (int i = 0; i < nn; i++) {
                    int z = neigh[i];
                    for (int j = i + 1; j < nn; j++) {
                        int zz = neigh[j];
                        if (data.adjacent(z,zz)) {
                            C4[x]++;
                            C4[y]++;
                            C4[z]++;
                            C4[zz]++;
                        }
                    }
                }
            }
        }
        
        // set up a system of equations relating orbits for every node
        int *common = (int *)S_alloc(n, sizeof(int));
        int *common_list = (int *)S_alloc(n, sizeof(int)), nc = 0;
        for (int x = 0; x < n; x++) {
            int64 f_12_14 = 0, f_10_13 = 0;
            int64 f_13_14 = 0, f_11_13 = 0;
            int64 f_7_11 = 0, f_5_8 = 0;
            int64 f_6_9 = 0, f_9_12 = 0, f_4_8 = 0, f_8_12 = 0;
            int64 f_14 = C4[x];
            
            for (int i = 0; i < nc; i++) {
                common[common_list[i]] = 0;
            }
            nc = 0;
            
            ORBIT(x, 0) = deg[x];
            // x - middle node
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int y = inc[x][nx1].first, ey = inc[x][nx1].second;
                for (int ny = 0;ny < deg[y];ny++) {
                    int z = inc[y][ny].first, ez = inc[y][ny].second;
                    if (data.adjacent(x,z)) { // triangle
                        if (z < y) {
                            f_12_14 += tri[ez] - 1;
                            f_10_13 += (deg[y] - 1 - tri[ez]) + (deg[z] - 1 - tri[ez]);
                        }
                    } else {
                        if (common[z]==0) {
                            common_list[nc++]=z;
                        }
                        common[z]++;
                    }
                }
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int z = inc[x][nx2].first, ez = inc[x][nx2].second;
                    if (data.adjacent(y, z)) { // triangle
                        ORBIT(x, 3)++;
                        f_13_14 += (tri[ey] -1) + (tri[ez] - 1);
                        f_11_13 += (deg[x] - 1 - tri[ey]) + (deg[x] - 1 - tri[ez]);
                    } else { // path
                        ORBIT(x, 2)++;
                        f_7_11 += (deg[x] - 1 - tri[ey] - 1) + (deg[x] - 1 - tri[ez] - 1);
                        f_5_8 += (deg[y] - 1 - tri[ey]) + (deg[z] - 1 - tri[ez]);
                    }
                }
            }
            // x - side node
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int y = inc[x][nx1].first, ey = inc[x][nx1].second;
                for (int ny = 0;ny < deg[y]; ny++) {
                    int z = inc[y][ny].first, ez = inc[y][ny].second;
                    if (x == z)
                        continue;
                    if (!data.adjacent(x,z)) { // path
                        ORBIT(x, 1)++;
                        f_6_9 += (deg[y] - 1 - tri[ey] - 1);
                        f_9_12 += tri[ez];
                        f_4_8 += (deg[z] - 1 - tri[ez]);
                        f_8_12 += (common[z] - 1);
                    }
                }
            }
            
            // solve system of equations
            ORBIT(x, 14) = (f_14);
            ORBIT(x, 13) = (f_13_14 - 6 * f_14) / 2;
            ORBIT(x, 12) = (f_12_14 - 3 * f_14);
            ORBIT(x, 11) = (f_11_13 - f_13_14 + 6 * f_14) / 2;
            ORBIT(x, 10) = (f_10_13 - f_13_14 + 6 * f_14);
            ORBIT(x, 9) = (f_9_12-2 * f_12_14 + 6 * f_14) / 2;
            ORBIT(x, 8) = (f_8_12-2 * f_12_14 + 6 * f_14) / 2;
            ORBIT(x, 7) = (f_13_14 + f_7_11 - f_11_13 - 6 * f_14) / 6;
            ORBIT(x, 6) = (2 * f_12_14 + f_6_9 - f_9_12 - 6 * f_14) / 2;
            ORBIT(x, 5) = (2 * f_12_14 + f_5_8 - f_8_12 - 6 * f_14);
            ORBIT(x, 4) = (2 * f_12_14 + f_4_8 - f_8_12 - 6 * f_14);
        }
    }
    catch (char const *s) {
        error(s);
    }
}


extern "C" void count5(PAIR *p_edges, int *dim_edges, int *orbits)
{
    try {
        int nn, nn2;
        GraphData data(p_edges, dim_edges);

        int const &n = data.n_nodes;
        int const &m = data.n_edges;
        PAIR const *const edges = data.edges;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;
        
        // precompute common nodes
        unordered_map<PAIR, int, hash_PAIR> common2;
        unordered_map<TRIPLE, int, hash_TRIPLE> common3;
        unordered_map<PAIR, int, hash_PAIR>::iterator common2_it;
        unordered_map<TRIPLE, int, hash_TRIPLE>::iterator common3_it;
        
        #define common3_get(x) (((common3_it = common3.find(x)) != common3.end()) ? (common3_it->second) : 0)
        #define common2_get(x) (((common2_it = common2.find(x)) != common2.end()) ? (common2_it->second) : 0)
        
        for (int x = 0; x < n; x++) {
            for (int n1 = 0; n1 < deg[x]; n1++) {
                int a = adj[x][n1];
                for (int n2 = n1 + 1; n2 < deg[x]; n2++) {
                    int b = adj[x][n2];
                    common2[PAIR(a, b)]++;
                    for (int n3 = n2 + 1; n3 < deg[x]; n3++) {
                        int c = adj[x][n3];
                        int st = data.adjacent(a, b) + data.adjacent(a, c) + data.adjacent(b, c);
                        if (st < 2)
                            continue;
                        common3[TRIPLE(a, b, c)]++;
                    }
                }
            }
        }
        
        // precompute triangles that span over edges
        int *tri = (int *)S_alloc(m, sizeof(int));
        for (int i = 0; i < m; i++) {
            int x = edges[i].a, y = edges[i].b;
            for (int xi = 0, yi = 0; xi < deg[x] && yi < deg[y]; ) {
                if (adj[x][xi] == adj[y][yi]) {
                    tri[i]++;
                    xi++;
                    yi++;
                }
                else if (adj[x][xi]<adj[y][yi]) {
                    xi++;
                }
                else {
                    yi++;
                }
            }
        }
        
        // count full graphlets
        int64 *C5 = (int64 *)S_alloc(n, sizeof(int64));
        int *neigh = (int *)R_alloc(n, sizeof(int));
        int *neigh2 = (int *)R_alloc(n, sizeof(int));
        for (int x = 0; x < n; x++) {
            for (int nx = 0; nx < deg[x]; nx++) {
                int y = adj[x][nx];
                if (y >= x)
                    break;
                nn = 0;
                for (int ny = 0; ny < deg[y]; ny++) {
                    int z = adj[y][ny];
                    if (z >= y)
                        break;
                    if (data.adjacent(x,z)) {
                        neigh[nn++] = z;
                    }
                }
                for (int i = 0; i < nn; i++) {
                    int z = neigh[i];
                    nn2 = 0;
                    for (int j = i + 1; j < nn; j++) {
                        int zz = neigh[j];
                        if (data.adjacent(z,zz)) {
                            neigh2[nn2++] = zz;
                        }
                    }
                    for (int i2 = 0; i2 < nn2; i2++) {
                        int zz = neigh2[i2];
                        for (int j2 = i2 + 1; j2 < nn2; j2++) {
                            int zzz = neigh2[j2];
                            if (data.adjacent(zz,zzz)) {
                                C5[x]++;
                                C5[y]++;
                                C5[z]++;
                                C5[zz]++;
                                C5[zzz]++;
                            }
                        }
                    }
                }
            }
        }
        
        int *common_x = (int *)S_alloc(n, sizeof(int));
        int *common_x_list = (int *)R_alloc(n, sizeof(int)), ncx = 0;
        int *common_a = (int *)S_alloc(n, sizeof(int));
        int *common_a_list = (int *)R_alloc(n, sizeof(int)), nca = 0;
        
        // set up a system of equations relating orbit counts
        for (int x = 0; x < n; x++) {
            for (int i = 0; i < ncx; i++) {
                common_x[common_x_list[i]] = 0;
            }
            ncx = 0;
            
            // smaller graphlets
            ORBIT(x, 0) = deg[x];
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int a = adj[x][nx1];
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = adj[x][nx2];
                    if (data.adjacent(a, b))
                        ORBIT(x, 3)++;
                    else
                        ORBIT(x, 2)++;
                }
                for (int na = 0; na < deg[a]; na++) {
                    int b = adj[a][na];
                    if (b != x && !data.adjacent(x, b)) {
                        ORBIT(x, 1)++;
                        if (common_x[b] == 0)
                            common_x_list[ncx++] = b;
                        common_x[b]++;
                    }
                }
            }
            
            int64 f_71 = 0, f_70 = 0, f_67 = 0, f_66 = 0, f_58 = 0, f_57 = 0; // 14
            int64 f_69 = 0, f_68 = 0, f_64 = 0, f_61 = 0, f_60 = 0, f_55 = 0, f_48 = 0, f_42 = 0, f_41 = 0; // 13
            int64 f_65 = 0, f_63 = 0, f_59 = 0, f_54 = 0, f_47 = 0, f_46 = 0, f_40 = 0; // 12
            int64 f_62 = 0, f_53 = 0, f_51 = 0, f_50 = 0, f_49 = 0, f_38 = 0, f_37 = 0, f_36 = 0; // 8
            int64 f_44 = 0, f_33 = 0, f_30 = 0, f_26 = 0; // 11
            int64 f_52 = 0, f_43 = 0, f_32 = 0, f_29 = 0, f_25 = 0; // 10
            int64 f_56 = 0, f_45 = 0, f_39 = 0, f_31 = 0, f_28 = 0, f_24 = 0; // 9
            int64 f_35 = 0, f_34 = 0, f_27 = 0, f_18 = 0, f_16 = 0, f_15 = 0; // 4
            int64 f_17 = 0; // 5
            int64 f_22 = 0, f_20 = 0, f_19 = 0; // 6
            int64 f_23 = 0, f_21 = 0; // 7
            
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int a = inc[x][nx1].first, xa = inc[x][nx1].second;
                
                for (int i = 0; i < nca; i++)
                    common_a[common_a_list[i]] = 0;
                nca = 0;
                for (int na = 0;na < deg[a]; na++) {
                    int b = adj[a][na];
                    for (int nb = 0; nb < deg[b]; nb++) {
                        int c = adj[b][nb];
                        if ((c==a) || data.adjacent(a, c))
                            continue;
                        if (!common_a[c])
                            common_a_list[nca++] = c;
                        common_a[c]++;
                    }
                }
                
                // x = orbit-14 (tetrahedron)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (!data.adjacent(a,b))
                        continue;
                    for (int nx3 = nx2+1; nx3 < deg[x]; nx3++) {
                        int c = inc[x][nx3].first, xc = inc[x][nx3].second;
                        if (!data.adjacent(a, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(x, 14)++;
                        f_70 += common3_get(TRIPLE(a, b, c)) - 1;
                        f_71 += (tri[xa] > 2 && tri[xb] > 2) ? common3_get(TRIPLE(x, a, b)) - 1 : 0;
                        f_71 += (tri[xa] > 2 && tri[xc] > 2) ? common3_get(TRIPLE(x, a, c)) - 1 : 0;
                        f_71 += (tri[xb] > 2 && tri[xc] > 2) ? common3_get(TRIPLE(x, b, c)) - 1 : 0;
                        f_67 += tri[xa] - 2 + tri[xb] - 2 + tri[xc] - 2;
                        f_66 += common2_get(PAIR(a, b)) - 2;
                        f_66 += common2_get(PAIR(a, c)) - 2;
                        f_66 += common2_get(PAIR(b, c)) - 2;
                        f_58 += deg[x] - 3;
                        f_57 += deg[a] - 3 + deg[b] - 3 + deg[c] - 3;
                    }
                }
                
                // x = orbit-13 (diamond)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nx3 = nx2 + 1; nx3 < deg[x]; nx3++) {
                        int c = inc[x][nx3].first, xc = inc[x][nx3].second;
                        if (!data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(x, 13)++;
                        f_69 += (tri[xb] > 1 && tri[xc] > 1) ? common3_get(TRIPLE(x, b, c)) - 1 : 0;
                        f_68 += common3_get(TRIPLE(a, b, c)) - 1;
                        f_64 += common2_get(PAIR(b, c)) - 2;
                        f_61 += tri[xb] - 1 + tri[xc] - 1;
                        f_60 += common2_get(PAIR(a, b)) - 1;
                        f_60 += common2_get(PAIR(a, c)) - 1;
                        f_55 += tri[xa] - 2;
                        f_48 += deg[b] - 2 + deg[c] - 2;
                        f_42 += deg[x] - 3;
                        f_41 += deg[a] - 3;
                    }
                }
                
                // x = orbit-12 (diamond)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int c = inc[a][na].first, ac = inc[a][na].second;
                        if ((c == x) || data.adjacent(x, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(x, 12)++;
                        f_65 += (tri[ac] > 1) ? common3_get(TRIPLE(a, b, c)) : 0;
                        f_63 += common_x[c] - 2;
                        f_59 += tri[ac] - 1 + common2_get(PAIR(b, c)) - 1;
                        f_54 += common2_get(PAIR(a, b)) - 2;
                        f_47 += deg[x] - 2;
                        f_46 += deg[c] - 2;
                        f_40 += deg[a] - 3 + deg[b] - 3;
                    }
                }
                
                // x = orbit-8 (cycle)
                for (int nx2  =nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (data.adjacent(a, b))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int c = inc[a][na].first, ac = inc[a][na].second;
                        if ((c == x) || data.adjacent(x, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(x, 8)++;
                        f_62 += (tri[ac] > 0) ? common3_get(TRIPLE(a, b, c)) : 0;
                        f_53 += tri[xa] + tri[xb];
                        f_51 += tri[ac] + common2_get(PAIR(c, b));
                        f_50 += common_x[c] - 2;
                        f_49 += common_a[b] - 2;
                        f_38 += deg[x] - 2;
                        f_37 += deg[a] - 2 + deg[b] - 2;
                        f_36 += deg[c] - 2;
                    }
                }
                
                // x = orbit-11 (paw)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nx3 = 0; nx3 < deg[x]; nx3++) {
                        int c = inc[x][nx3].first, xc = inc[x][nx3].second;
                        if ((c == a) || (c==b) || data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(x, 11)++;
                        f_44 += tri[xc];
                        f_33 += deg[x] - 3;
                        f_30 += deg[c] - 1;
                        f_26 += deg[a] - 2 + deg[b] - 2;
                    }
                }
                
                // x = orbit-10 (paw)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nb = 0; nb < deg[b]; nb++) {
                        int c = inc[b][nb].first, bc = inc[b][nb].second;
                        if ((c == x) || (c == a) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(x, 10)++;
                        f_52 += common_a[c] - 1;
                        f_43 += tri[bc];
                        f_32 += deg[b] - 3;
                        f_29 += deg[c] - 1;
                        f_25 += deg[a] - 2;
                    }
                }
                
                // x = orbit-9 (paw)
                for (int na1 = 0; na1 < deg[a]; na1++) {
                    int b = inc[a][na1].first, ab = inc[a][na1].second;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int na2 = na1 + 1; na2 < deg[a]; na2++) {
                        int c = inc[a][na2].first, ac = inc[a][na2].second;
                        if ((c == x) || !data.adjacent(b, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(x, 9)++;
                        f_56 += (tri[ab] > 1 && tri[ac] > 1) ? common3_get(TRIPLE(a, b, c)) : 0;
                        f_45 += common2_get(PAIR(b, c)) - 1;
                        f_39 += tri[ab] - 1 + tri[ac] - 1;
                        f_31 += deg[a] - 3;
                        f_28 += deg[x] - 1;
                        f_24 += deg[b] - 2 + deg[c] - 2;
                    }
                }
                
                // x = orbit-4 (path)
                for (int na = 0; na < deg[a]; na++) {
                    int b = inc[a][na].first, ab = inc[a][na].second;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int nb = 0;nb < deg[b]; nb++) {
                        int c = inc[b][nb].first, bc = inc[b][nb].second;
                        if ((c == a) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(x, 4)++;
                        f_35 += common_a[c] - 1;
                        f_34 += common_x[c];
                        f_27 += tri[bc];
                        f_18 += deg[b] - 2;
                        f_16 += deg[x] - 1;
                        f_15 += deg[c] - 1;
                    }
                }
                
                // x = orbit-5 (path)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if ((b==a) || data.adjacent(a, b))
                        continue;
                    for (int nb = 0; nb < deg[b]; nb++) {
                        int c = inc[b][nb].first, bc = inc[b][nb].second;
                        if ((c == x) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(x, 5)++;
                        f_17 += deg[a] - 1;
                    }
                }
                
                // x = orbit-6 (claw)
                for (int na1 = 0;na1 < deg[a]; na1++) {
                    int b = inc[a][na1].first, ab = inc[a][na1].second;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int na2 = na1 + 1; na2 < deg[a]; na2++) {
                        int c = inc[a][na2].first, ac = inc[a][na2].second;
                        if ((c == x) || data.adjacent(x,c) || data.adjacent(b,c))
                            continue;
                        ORBIT(x, 6)++;
                        f_22 += deg[a] - 3;
                        f_20 += deg[x] - 1;
                        f_19 += deg[b] - 1 + deg[c] - 1;
                    }
                }
                
                // x = orbit-7 (claw)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int b = inc[x][nx2].first, xb = inc[x][nx2].second;
                    if (data.adjacent(a, b))
                        continue;
                    for (int nx3 = nx2 + 1; nx3 < deg[x]; nx3++) {
                        int c = inc[x][nx3].first, xc = inc[x][nx3].second;
                        if (data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(x, 7)++;
                        f_23 += deg[x] - 3;
                        f_21 += deg[a] - 1 + deg[b] - 1 + deg[c] - 1;
                    }
                }
            }
            
            // solve equations
            ORBIT(x, 72) = C5[x];
            ORBIT(x, 71) = (f_71 - 12 * ORBIT(x, 72)) / 2;
            ORBIT(x, 70) = (f_70 - 4 * ORBIT(x, 72));
            ORBIT(x, 69) = (f_69 - 2 * ORBIT(x, 71))/4;
            ORBIT(x, 68) = (f_68 - 2 * ORBIT(x, 71));
            ORBIT(x, 67) = (f_67 - 12 * ORBIT(x, 72) - 4 * ORBIT(x, 71));
            ORBIT(x, 66) = (f_66 - 12 * ORBIT(x, 72) - 2 * ORBIT(x, 71) - 3 * ORBIT(x, 70));
            ORBIT(x, 65) = (f_65 - 3 * ORBIT(x, 70)) / 2;
            ORBIT(x, 64) = (f_64 - 2 * ORBIT(x, 71) - 4 * ORBIT(x, 69) - 1 * ORBIT(x, 68));
            ORBIT(x, 63) = (f_63 - 3 * ORBIT(x, 70) - 2 * ORBIT(x, 68));
            ORBIT(x, 62) = (f_62 - 1 * ORBIT(x, 68)) / 2;
            ORBIT(x, 61) = (f_61 - 4 * ORBIT(x, 71) - 8 * ORBIT(x, 69) - 2 * ORBIT(x, 67)) / 2;
            ORBIT(x, 60) = (f_60 - 4 * ORBIT(x, 71) - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 67));
            ORBIT(x, 59) = (f_59 - 6 * ORBIT(x, 70) - 2 * ORBIT(x, 68) - 4 * ORBIT(x, 65));
            ORBIT(x, 58) = (f_58 - 4 * ORBIT(x, 72) - 2 * ORBIT(x, 71) - 1 * ORBIT(x, 67));
            ORBIT(x, 57) = (f_57 - 12 * ORBIT(x, 72) - 4 * ORBIT(x, 71) - 3 * ORBIT(x, 70) - 1 * ORBIT(x, 67) - 2 * ORBIT(x, 66));
            ORBIT(x, 56) = (f_56 - 2 * ORBIT(x, 65)) / 3;
            ORBIT(x, 55) = (f_55 - 2 * ORBIT(x, 71) - 2 * ORBIT(x, 67)) / 3;
            ORBIT(x, 54) = (f_54 - 3 * ORBIT(x, 70) - 1 * ORBIT(x, 66) - 2 * ORBIT(x, 65)) / 2;
            ORBIT(x, 53) = (f_53 - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 64) - 2 * ORBIT(x, 63));
            ORBIT(x, 52) = (f_52 - 2 * ORBIT(x, 66) - 2 * ORBIT(x, 64) - 1 * ORBIT(x, 59)) / 2;
            ORBIT(x, 51) = (f_51 - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 63) - 4 * ORBIT(x, 62));
            ORBIT(x, 50) = (f_50 - 1 * ORBIT(x, 68) - 2 * ORBIT(x, 63)) / 3;
            ORBIT(x, 49) = (f_49 - 1 * ORBIT(x, 68) - 1 * ORBIT(x, 64) - 2 * ORBIT(x, 62)) / 2;
            ORBIT(x, 48) = (f_48 - 4 * ORBIT(x, 71) - 8 * ORBIT(x, 69) - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 67) - 2 * ORBIT(x, 64) - 2 * ORBIT(x, 61) - 1 * ORBIT(x, 60));
            ORBIT(x, 47) = (f_47 - 3 * ORBIT(x, 70) - 2 * ORBIT(x, 68) - 1 * ORBIT(x, 66) - 1 * ORBIT(x, 63) - 1 * ORBIT(x, 60));
            ORBIT(x, 46) = (f_46 - 3 * ORBIT(x, 70) - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 65) - 1 * ORBIT(x, 63) - 1 * ORBIT(x, 59));
            ORBIT(x, 45) = (f_45 - 2 * ORBIT(x, 65) - 2 * ORBIT(x, 62) - 3 * ORBIT(x, 56));
            ORBIT(x, 44) = (f_44 - 1 * ORBIT(x, 67) - 2 * ORBIT(x, 61))/4;
            ORBIT(x, 43) = (f_43 - 2 * ORBIT(x, 66) - 1 * ORBIT(x, 60) - 1 * ORBIT(x, 59)) / 2;
            ORBIT(x, 42) = (f_42 - 2 * ORBIT(x, 71) - 4 * ORBIT(x, 69) - 2 * ORBIT(x, 67) - 2 * ORBIT(x, 61) - 3 * ORBIT(x, 55));
            ORBIT(x, 41) = (f_41 - 2 * ORBIT(x, 71) - 1 * ORBIT(x, 68) - 2 * ORBIT(x, 67) - 1 * ORBIT(x, 60) - 3 * ORBIT(x, 55));
            ORBIT(x, 40) = (f_40 - 6 * ORBIT(x, 70) - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 66) - 4 * ORBIT(x, 65) - 1 * ORBIT(x, 60) - 1 * ORBIT(x, 59) - 4 * ORBIT(x, 54));
            ORBIT(x, 39) = (f_39 - 4 * ORBIT(x, 65) - 1 * ORBIT(x, 59) - 6 * ORBIT(x, 56)) / 2;
            ORBIT(x, 38) = (f_38 - 1 * ORBIT(x, 68) - 1 * ORBIT(x, 64) - 2 * ORBIT(x, 63) - 1 * ORBIT(x, 53) - 3 * ORBIT(x, 50));
            ORBIT(x, 37) = (f_37 - 2 * ORBIT(x, 68) - 2 * ORBIT(x, 64) - 2 * ORBIT(x, 63) - 4 * ORBIT(x, 62) - 1 * ORBIT(x, 53) - 1 * ORBIT(x, 51) - 4 * ORBIT(x, 49));
            ORBIT(x, 36) = (f_36 - 1 * ORBIT(x, 68) - 2 * ORBIT(x, 63) - 2 * ORBIT(x, 62) - 1 * ORBIT(x, 51) - 3 * ORBIT(x, 50));
            ORBIT(x, 35) = (f_35 - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 52) - 2 * ORBIT(x, 45)) / 2;
            ORBIT(x, 34) = (f_34 - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 52) - 1 * ORBIT(x, 51)) / 2;
            ORBIT(x, 33) = (f_33 - 1 * ORBIT(x, 67) - 2 * ORBIT(x, 61) - 3 * ORBIT(x, 58) - 4 * ORBIT(x, 44) - 2 * ORBIT(x, 42)) / 2;
            ORBIT(x, 32) = (f_32 - 2 * ORBIT(x, 66) - 1 * ORBIT(x, 60) - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 57) - 2 * ORBIT(x, 43) - 2 * ORBIT(x, 41) - 1 * ORBIT(x, 40)) / 2;
            ORBIT(x, 31) = (f_31 - 2 * ORBIT(x, 65) - 1 * ORBIT(x, 59) - 3 * ORBIT(x, 56) - 1 * ORBIT(x, 43) - 2 * ORBIT(x, 39));
            ORBIT(x, 30) = (f_30 - 1 * ORBIT(x, 67) - 1 * ORBIT(x, 63) - 2 * ORBIT(x, 61) - 1 * ORBIT(x, 53) - 4 * ORBIT(x, 44));
            ORBIT(x, 29) = (f_29 - 2 * ORBIT(x, 66) - 2 * ORBIT(x, 64) - 1 * ORBIT(x, 60) - 1 * ORBIT(x, 59) - 1 * ORBIT(x, 53) - 2 * ORBIT(x, 52) - 2 * ORBIT(x, 43));
            ORBIT(x, 28) = (f_28 - 2 * ORBIT(x, 65) - 2 * ORBIT(x, 62) - 1 * ORBIT(x, 59) - 1 * ORBIT(x, 51) - 1 * ORBIT(x, 43));
            ORBIT(x, 27) = (f_27 - 1 * ORBIT(x, 59) - 1 * ORBIT(x, 51) - 2 * ORBIT(x, 45)) / 2;
            ORBIT(x, 26) = (f_26 - 2 * ORBIT(x, 67) - 2 * ORBIT(x, 63) - 2 * ORBIT(x, 61) - 6 * ORBIT(x, 58) - 1 * ORBIT(x, 53) - 2 * ORBIT(x, 47) - 2 * ORBIT(x, 42));
            ORBIT(x, 25) = (f_25 - 2 * ORBIT(x, 66) - 2 * ORBIT(x, 64) - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 57) - 2 * ORBIT(x, 52) - 1 * ORBIT(x, 48) - 1 * ORBIT(x, 40)) / 2;
            ORBIT(x, 24) = (f_24 - 4 * ORBIT(x, 65) - 4 * ORBIT(x, 62) - 1 * ORBIT(x, 59) - 6 * ORBIT(x, 56) - 1 * ORBIT(x, 51) - 2 * ORBIT(x, 45) - 2 * ORBIT(x, 39));
            ORBIT(x, 23) = (f_23 - 1 * ORBIT(x, 55) - 1 * ORBIT(x, 42) - 2 * ORBIT(x, 33))/4;
            ORBIT(x, 22) = (f_22 - 2 * ORBIT(x, 54) - 1 * ORBIT(x, 40) - 1 * ORBIT(x, 39) - 1 * ORBIT(x, 32) - 2 * ORBIT(x, 31)) / 3;
            ORBIT(x, 21) = (f_21 - 3 * ORBIT(x, 55) - 3 * ORBIT(x, 50) - 2 * ORBIT(x, 42) - 2 * ORBIT(x, 38) - 2 * ORBIT(x, 33));
            ORBIT(x, 20) = (f_20 - 2 * ORBIT(x, 54) - 2 * ORBIT(x, 49) - 1 * ORBIT(x, 40) - 1 * ORBIT(x, 37) - 1 * ORBIT(x, 32));
            ORBIT(x, 19) = (f_19 - 4 * ORBIT(x, 54) - 4 * ORBIT(x, 49) - 1 * ORBIT(x, 40) - 2 * ORBIT(x, 39) - 1 * ORBIT(x, 37) - 2 * ORBIT(x, 35) - 2 * ORBIT(x, 31));
            ORBIT(x, 18) = (f_18 - 1 * ORBIT(x, 59) - 1 * ORBIT(x, 51) - 2 * ORBIT(x, 46) - 2 * ORBIT(x, 45) - 2 * ORBIT(x, 36) - 2 * ORBIT(x, 27) - 1 * ORBIT(x, 24)) / 2;
            ORBIT(x, 17) = (f_17 - 1 * ORBIT(x, 60) - 1 * ORBIT(x, 53) - 1 * ORBIT(x, 51) - 1 * ORBIT(x, 48) - 1 * ORBIT(x, 37) - 2 * ORBIT(x, 34) - 2 * ORBIT(x, 30)) / 2;
            ORBIT(x, 16) = (f_16 - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 52) - 1 * ORBIT(x, 51) - 2 * ORBIT(x, 46) - 2 * ORBIT(x, 36) - 2 * ORBIT(x, 34) - 1 * ORBIT(x, 29));
            ORBIT(x, 15) = (f_15 - 1 * ORBIT(x, 59) - 2 * ORBIT(x, 52) - 1 * ORBIT(x, 51) - 2 * ORBIT(x, 45) - 2 * ORBIT(x, 35) - 2 * ORBIT(x, 34) - 2 * ORBIT(x, 27));
        }
    }
    catch (char const *s) {
        error(s);
    }
    
}



/** count edge orbits of graphlets on max 4 nodes */
extern "C" void ecount4(PAIR *p_edges, int *dim_edges, int *orbits) {
    GraphData data(p_edges, dim_edges);
    
    int const &n = data.n_nodes;
    int const &m = data.n_edges;
    PAIR const *const edges = data.edges;
    int const *const deg = data.deg;
    int const *const *const adj = data.adj;
    PII const *const *const inc = data.inc;

	// precompute triangles that span over edges
	int *tri = (int*)S_alloc(m, sizeof(int));
	for (int i = 0; i < m; i++) {
		int const &x = edges[i].a, &y = edges[i].b;
		for (int xi = 0,yi = 0; xi < deg[x] && yi < deg[y]; ) {
			if (adj[x][xi] == adj[y][yi]) {
                tri[i]++;
                xi++;
                yi++;
            }
			else if (adj[x][xi] < adj[y][yi]) {
                xi++;
            }
			else {
                yi++;
            }
		}
	}
    
	// count full graphlets
	int64 *C4 = (int64 *)S_alloc(m, sizeof(int64));
	int *neighx = (int *)R_alloc(n, sizeof(int)); // lookup table - edges to neighbors of x
	memset(neighx, -1, n * sizeof(int));
	int *neigh = (int *)R_alloc(n, sizeof(int)), nn; // lookup table - common neighbors of x and y
	PII *neigh_edges = (PII *)R_alloc(n, sizeof(PII)); // list of common neighbors of x and y
	for (int x = 0; x < n; x++) {
		for (int nx = 0; nx < deg[x]; nx++) {
			int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
			neighx[y] = xy;
		}
		for (int nx = 0; nx < deg[x]; nx++) {
			int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
			if (y >= x)
                break;
			nn = 0;
			for (int ny = 0; ny < deg[y]; ny++) {
				int const &z = inc[y][ny].first, &yz = inc[y][ny].second;
				if (z >= y)
                    break;
				if (neighx[z] == -1)
                    continue;
				int const &xz = neighx[z];
				neigh[nn] = z;
				neigh_edges[nn] = PII(xz, yz);
				nn++;
			}
			for (int i = 0; i < nn; i++) {
				int z = neigh[i], xz = neigh_edges[i].first, yz = neigh_edges[i].second;
				for (int j = i + 1; j < nn; j++) {
					int const &w = neigh[j], &xw = neigh_edges[j].first, &yw = neigh_edges[j].second;
					if (data.adjacent(z, w)) {
						C4[xy]++;
						C4[xz]++;
                        C4[yz]++;
						C4[xw]++;
                        C4[yw]++;
						// another iteration to count this last(smallest) edge instead of calling getEdgeId
						//int zw=getEdgeId(z,w); C4[zw]++;
					}
				}
			}
		}
		for (int nx = 0; nx < deg[x]; nx++) {
			int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
			neighx[y] = -1;
		}
	}
    
	// count full graphlets for the smallest edge
	for (int x = 0; x < n; x++) {
		for (int nx = deg[x] - 1; nx >= 0; nx--) {
			int const &y = inc[x][nx].first, xy = inc[x][nx].second;
			if (y <= x)
                break;
			nn = 0;
			for (int ny = deg[y] - 1; ny >= 0; ny--) {
				int z = adj[y][ny];
				if (z <= y)
                    break;
				if (!data.adjacent(x, z)) continue;
				neigh[nn++] = z;
			}
			for (int i = 0; i < nn; i++) {
				int z = neigh[i];
				for (int j = i + 1; j < nn; j++) {
					int zz = neigh[j];
					if (data.adjacent(z, zz)) {
						C4[xy]++;
					}
				}
			}
		}
	}
    
	// set up a system of equations relating orbits for every node
	int *common = (int *)S_alloc(n, sizeof(int));
	int *common_list = (int *)R_alloc(n, sizeof(int)), nc = 0;
	for (int x = 0; x < n; x++) {
		// common nodes of x and some other node
		for (int i = 0; i < nc; i++)
            common[common_list[i]] = 0;
		nc = 0;
		for (int nx = 0; nx<deg[x];nx++) {
			int const &y = adj[x][nx];
			for (int ny = 0; ny < deg[y]; ny++) {
				int z = adj[y][ny];
				if (z == x)
                    continue;
				if (common[z] == 0)
                    common_list[nc++]=z;
				common[z]++;
			}
		}
        
		for (int nx = 0; nx < deg[x]; nx++) {
			int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
			int const &e = xy;
			for (int n1 = 0; n1 < deg[x]; n1++) {
				int z = inc[x][n1].first, xz = inc[x][n1].second;
				if (z == y)
                    continue;
				if (data.adjacent(y, z)) { // triangle
					if (x < y) {
						ORBIT(e, 1)++;
						ORBIT(e, 10) += tri[xy] - 1;
						ORBIT(e, 7) += deg[z] - 2;
					}
					ORBIT(e, 9) += tri[xz] - 1;
					ORBIT(e, 8) += deg[x] - 2;
				}
			}
			for (int n1 = 0; n1 < deg[y]; n1++) {
				int const &z = inc[y][n1].first, yz = inc[y][n1].second;
				if (z == x)
                    continue;
				if (!data.adjacent(x, z)) { // path x-y-z
					ORBIT(e, 0)++;
					ORBIT(e, 6) += tri[yz];
					ORBIT(e, 5) += common[z]  - 1;
					ORBIT(e, 4) += deg[y] - 2;
					ORBIT(e, 3) += deg[x] - 1;
					ORBIT(e, 2) += deg[z] - 1;
				}
			}
		}
	}
	// solve system of equations
	for (int e = 0; e < m; e++) {
		ORBIT(e, 11) = C4[e];
		ORBIT(e, 10) = (ORBIT(e, 10)- 2 * ORBIT(e, 11)) / 2;
		ORBIT(e, 9) = (ORBIT(e, 9) - 4 * ORBIT(e, 11));
		ORBIT(e, 8) = (ORBIT(e, 8) - ORBIT(e, 9) - 4 * ORBIT(e, 10) - 4 * ORBIT(e, 11));
		ORBIT(e, 7) = (ORBIT(e, 7) - ORBIT(e, 9) - 2 * ORBIT(e, 11));
		ORBIT(e, 6) = (ORBIT(e, 6) - ORBIT(e, 9)) / 2;
		ORBIT(e, 5) = (ORBIT(e, 5) - ORBIT(e, 9)) / 2;
		ORBIT(e, 4) = (ORBIT(e, 4) - 2 * ORBIT(e, 6) - ORBIT(e, 8) - ORBIT(e, 9)) / 2;
		ORBIT(e, 3) = (ORBIT(e, 3) - 2 * ORBIT(e, 5) - ORBIT(e, 8) - ORBIT(e, 9)) / 2;
		ORBIT(e, 2) = (ORBIT(e, 2) - 2 * ORBIT(e, 5) - 2 * ORBIT(e, 6) - ORBIT(e, 9));
	}
}
