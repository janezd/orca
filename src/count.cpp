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

struct TIII {
    int first, second, third;
    inline TIII(int const f, int const s, int const t)
    : first(f), second(s), third(t)
    {}
};

struct PAIR {
	int a, b;

    inline PAIR(int const aa, int const bb)
    : a(min(aa, bb)), b(max(aa, bb))
    {}

    inline bool operator <(const PAIR &other) const {
        return (a < other.a) || (a == other.a && b < other.b);
    }

    inline bool operator ==(const PAIR &other) const {
        return a == other.a && b == other.b;
    }
};

struct hash_PAIR {
    inline size_t operator()(PAIR const &x) const {
        return (x.a << 8) ^ (x.b << 0);
    }
};



struct TRIPLE {
	int a, b, c;

	TRIPLE(int const a0, int const b0, int const c0)
    : a(a0), b(b0), c(c0) {
		if (a > b)
            swap(a, b);
		if (b > c)
            swap(b, c);
		if (a > b)
            swap(a, b);
	}

    inline bool operator <(TRIPLE const &other) const {
        return (a < other.a) ||
               (a == other.a && (b < other.b ||
                                 (b == other.b && c < other.c)));
    }

    inline bool operator ==(TRIPLE const &other) const {
        return a == other.a && b == other.b && c == other.c;
    }
};

struct hash_TRIPLE {
	inline size_t operator ()(TRIPLE const &x) const {
		return (x.a << 16) ^ (x.b << 8) ^ (x.c << 0);
	}
};


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

    GraphData(PAIR * const edges, int const * const dim_edges);
    int const *triangles() const;
    void common_2_3(
        unordered_map<PAIR, int, hash_PAIR> &common2,
        unordered_map<TRIPLE, int, hash_TRIPLE> &common3) const;

    inline bool adjacent_list(int const x, int const y) const
    {
        return binary_search(adj[x], adj[x] + deg[x], y);
    }

    inline bool adjacent_matrix(int const x, int const y) const
    {
        return adj_matrix[(x * n_nodes + y) / adj_chunk] & (1 << ((x * n_nodes + y) % adj_chunk));
    }

    inline bool adjacent(int const x, int const y) const {
        return adj_matrix ? adjacent_matrix(x, y) : adjacent_list(x, y);
    }

    inline int getEdgeId(int const x, int const y) const {
        return inc[x][lower_bound(adj[x], adj[x] + deg[x], y) - adj[x]].second;
    }

};


GraphData::GraphData(PAIR * const p_edges, int const * const dim_edges)
: n_nodes(0),
  n_edges(dim_edges[1]),
  d_max(0),
  edges(p_edges),
  edges_end(edges + dim_edges[1]),
  deg(NULL),
  inc(NULL),
  adj_matrix(NULL)
{
    if (dim_edges[0] != 2) {
        throw "Incorrect size of edges matrix";
    }
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
        if (edge->a == edge->b) {
            throw "Graph contains loops (edges to the same node)";
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
//    if ((int64)n_nodes * n_nodes < 100LL * 1024 * 1024 * 8) {
    if (n_nodes < 30000) {
        adj_matrix = (int *)S_alloc((n_nodes * n_nodes) / adj_chunk + 1, sizeof(int));
        for (edge = edges; edge != edges_end; edge++) {
            int const &a = edge->a, &b = edge->b;
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
    int * const d = (int *)S_alloc(n_nodes, sizeof(int));
    for (i = 0; i < n_edges; i++) {
        int const &a = edges[i].a, &b = edges[i].b;
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
        for (int j = 1; j < deg[i]; j++) {
            if (adj[i][j] == adj[i][j - 1])
                throw "Graph contains multiple edges between same nodes";
        }
    }
}


int const *GraphData::triangles() const {
    // precompute triangles that span over edges
    int * const tri = (int *)S_alloc(n_edges, sizeof(int));
    for (int i = 0; i < n_edges; i++) {
        int const &x = edges[i].a, &y = edges[i].b;
        for (int xi = 0, yi = 0; xi < deg[x] && yi < deg[y]; ) {
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
    return tri;
}


void GraphData::common_2_3(
        unordered_map<PAIR, int, hash_PAIR> &common2,
        unordered_map<TRIPLE, int, hash_TRIPLE> &common3) const {
    for (int x = 0; x < n_nodes; x++) {
        for (int n1 = 0; n1 < deg[x]; n1++) {
            int const &a = adj[x][n1];
            for (int n2 = n1 + 1; n2 < deg[x]; n2++) {
                int const &b = adj[x][n2];
                common2[PAIR(a, b)]++;
                for (int n3 = n2 + 1; n3 < deg[x]; n3++) {
                    int const &c = adj[x][n3];
                    int const st = adjacent(a, b) + adjacent(a, c) + adjacent(b, c);
                    if (st < 2)
                        continue;
                    common3[TRIPLE(a,b,c)]++;
                }
            }
        }
    }
}

#define ORBIT(orb)  orbits[x + orb * n]
#define EORBIT(orb) orbits[e + orb * m]

#define common3_get(x) (((common3_it = common3.find(x)) != common3.end()) ? (common3_it->second) : 0)
#define common2_get(x) (((common2_it = common2.find(x)) != common2.end()) ? (common2_it->second) : 0)



/** count graphlets on 4 nodes */

extern "C" void count4(PAIR * const p_edges, int const * const dim_edges, double * const orbits)
{
    try {
        int nn;
        GraphData data(p_edges, dim_edges);
        int const * const tri = data.triangles();

        int const &n = data.n_nodes;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;


        // count complete graphlets on 4 nodes
        int64 * const C4 = (int64 *)S_alloc(data.n_nodes, sizeof(int64));
        int * const neigh = (int *)S_alloc(n, sizeof(int));

        for (int x = 0; x < data.n_nodes; x++) {
            for (int nx = 0; nx < data.deg[x]; nx++) {
                int const &y = adj[x][nx];
                if (y >= x)
                    break;
                nn = 0;
                for (int ny = 0; ny < data.deg[y]; ny++) {
                    int const &z = adj[y][ny];
                    if (z >= y)
                        break;
                    if (!data.adjacent(x, z))
                        continue;
                    neigh[nn++] = z;
                }
                for (int i = 0; i < nn; i++) {
                    int const &z = neigh[i];
                    for (int j = i + 1; j < nn; j++) {
                        int const &zz = neigh[j];
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
        int * const common = (int *)S_alloc(n, sizeof(int));
        int * const common_list = (int *)S_alloc(n, sizeof(int)), nc = 0;
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

            ORBIT(0) = deg[x];
            // x - middle node
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int const &y = inc[x][nx1].first, &ey = inc[x][nx1].second;
                for (int ny = 0;ny < deg[y];ny++) {
                    int const &z = inc[y][ny].first, &ez = inc[y][ny].second;
                    if (data.adjacent(x,z)) { // triangle
                        if (z < y) {
                            f_12_14 += tri[ez] - 1; // o_{12} + 3o_{14}
                            f_10_13 += (deg[y] - 1 - tri[ez]) + (deg[z] - 1 - tri[ez]); // o_{10} + 2o_{13}
                        }
                    } else {
                        if (common[z]==0) {
                            common_list[nc++]=z;
                        }
                        common[z]++;
                    }
                }
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &z = inc[x][nx2].first, &ez = inc[x][nx2].second;
                    if (data.adjacent(y, z)) { // triangle
                        ORBIT(3)++;
                        f_13_14 += (tri[ey] -1) + (tri[ez] - 1); // 2o_{13} + 6o_{14}
                        f_11_13 += (deg[x] - 1 - tri[ey]) + (deg[x] - 1 - tri[ez]); // 2o_{11} + 2o_{13}
                    } else { // path
                        ORBIT(2)++;
                        f_7_11 += (deg[x] - 1 - tri[ey] - 1) + (deg[x] - 1 - tri[ez] - 1); // 6o_{7} + 2o_{11}
                        f_5_8 += (deg[y] - 1 - tri[ey]) + (deg[z] - 1 - tri[ez]); // o_{5} + 2o_{8}
                    }
                }
            }
            // x - side node
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int const &y = inc[x][nx1].first, &ey = inc[x][nx1].second;
                for (int ny = 0;ny < deg[y]; ny++) {
                    int const &z = inc[y][ny].first, &ez = inc[y][ny].second;
                    if (x == z)
                        continue;
                    if (!data.adjacent(x,z)) { // path
                        ORBIT(1)++;
                        f_6_9 += (deg[y] - 1 - tri[ey] - 1); // 2o_{6} + 2o_{9}
                        f_9_12 += tri[ez]; // 2o_{9} + 2o_{12}
                        f_4_8 += (deg[z] - 1 - tri[ez]); // o_{4} + 2o_{8}
                        f_8_12 += (common[z] - 1); // 2o_{8} + 2o_{12}
                    }
                }
            }

            // solve system of equations
            ORBIT(14) = (f_14);
            ORBIT(13) = (f_13_14 - 6 * f_14) / 2;
            ORBIT(12) = (f_12_14 - 3 * f_14);
            ORBIT(11) = (f_11_13 - f_13_14 + 6 * f_14) / 2;
            ORBIT(10) = (f_10_13 - f_13_14 + 6 * f_14);
            ORBIT(9) = (f_9_12-2 * f_12_14 + 6 * f_14) / 2;
            ORBIT(8) = (f_8_12-2 * f_12_14 + 6 * f_14) / 2;
            ORBIT(7) = (f_13_14 + f_7_11 - f_11_13 - 6 * f_14) / 6;
            ORBIT(6) = (2 * f_12_14 + f_6_9 - f_9_12 - 6 * f_14) / 2;
            ORBIT(5) = (2 * f_12_14 + f_5_8 - f_8_12 - 6 * f_14);
            ORBIT(4) = (2 * f_12_14 + f_4_8 - f_8_12 - 6 * f_14);
        }
    }
    catch (char const *s) {
        error(s);
    }
}


/** count edge orbits of graphlets on max 4 nodes */
extern "C" void ecount4(PAIR * const p_edges, int const * const dim_edges, double * const orbits) {
    try {
        GraphData data(p_edges, dim_edges);
        int const * const tri = data.triangles();

        int const &n = data.n_nodes;
        int const &m = data.n_edges;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;

        // count complete graphlets on four nodes
        int64 * const C4 = (int64 *)S_alloc(m, sizeof(int64));
        int * const neighx = (int *)R_alloc(n, sizeof(int)); // lookup table - edges to neighbors of x
        memset(neighx, -1, n * sizeof(int));
        int * const neigh = (int *)R_alloc(n, sizeof(int)), nn; // lookup table - common neighbors of x and y
        PII * const neigh_edges = (PII *)R_alloc(n, sizeof(PII)); // list of common neighbors of x and y
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
                    int const &z = neigh[i], &xz = neigh_edges[i].first, &yz = neigh_edges[i].second;
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
                int const &y = inc[x][nx].first;
                neighx[y] = -1;
            }
        }

        // count full graphlets for the smallest edge
        for (int x = 0; x < n; x++) {
            for (int nx = deg[x] - 1; nx >= 0; nx--) {
                int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
                if (y <= x)
                    break;
                nn = 0;
                for (int ny = deg[y] - 1; ny >= 0; ny--) {
                    int const &z = adj[y][ny];
                    if (z <= y)
                        break;
                    if (!data.adjacent(x, z)) continue;
                    neigh[nn++] = z;
                }
                for (int i = 0; i < nn; i++) {
                    int const &z = neigh[i];
                    for (int j = i + 1; j < nn; j++) {
                        int const &zz = neigh[j];
                        if (data.adjacent(z, zz)) {
                            C4[xy]++;
                        }
                    }
                }
            }
        }

        // set up a system of equations relating orbits for every node
        int *const common = (int *)S_alloc(n, sizeof(int));
        int *const common_list = (int *)R_alloc(n, sizeof(int)), nc = 0;
        for (int x = 0; x < n; x++) {
            // common nodes of x and some other node
            for (int i = 0; i < nc; i++)
                common[common_list[i]] = 0;
            nc = 0;
            for (int nx = 0; nx<deg[x];nx++) {
                int const &y = adj[x][nx];
                for (int ny = 0; ny < deg[y]; ny++) {
                    int const &z = adj[y][ny];
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
                    int const &z = inc[x][n1].first, &xz = inc[x][n1].second;
                    if (z == y)
                        continue;
                    if (data.adjacent(y, z)) { // triangle
                        if (x < y) {
                            EORBIT(1)++;
                            EORBIT(10) += tri[xy] - 1; // 2e_{10}+2e_{11}
                            EORBIT(7) += deg[z] - 2; // e_{7}+e_{9}+2e_{11}
                        }
                        EORBIT(9) += tri[xz] - 1; // e_{9}+4e_{11}
                        EORBIT(8) += deg[x] - 2; // e_{8}+e_{9}+4e_{10}+4e_{11}
                    }
                }
                for (int n1 = 0; n1 < deg[y]; n1++) {
                    int const &z = inc[y][n1].first, &yz = inc[y][n1].second;
                    if (z == x)
                        continue;
                    if (!data.adjacent(x, z)) { // path x-y-z
                        EORBIT(0)++;
                        EORBIT(6) += tri[yz]; // 2e_{6}+e_{9}
                        EORBIT(5) += common[z]  - 1; // 2e_{5}+e_{9}
                        EORBIT(4) += deg[y] - 2; // 2e_{4}+2e_{6}+e_{8}+e_{9}
                        EORBIT(3) += deg[x] - 1; // 2e_{3}+2e_{5}+e_{8}+e_{9}
                        EORBIT(2) += deg[z] - 1; // e_{2}+2e_{5}+2e_{6}+e_{9}
                    }
                }
            }
        }
        // solve system of equations
        for (int e = 0; e < m; e++) {
            EORBIT(11) = C4[e];
            EORBIT(10) = (EORBIT(10)- 2 * EORBIT(11)) / 2;
            EORBIT(9) = (EORBIT(9) - 4 * EORBIT(11));
            EORBIT(8) = (EORBIT(8) - EORBIT(9) - 4 * EORBIT(10) - 4 * EORBIT(11));
            EORBIT(7) = (EORBIT(7) - EORBIT(9) - 2 * EORBIT(11));
            EORBIT(6) = (EORBIT(6) - EORBIT(9)) / 2;
            EORBIT(5) = (EORBIT(5) - EORBIT(9)) / 2;
            EORBIT(4) = (EORBIT(4) - 2 * EORBIT(6) - EORBIT(8) - EORBIT(9)) / 2;
            EORBIT(3) = (EORBIT(3) - 2 * EORBIT(5) - EORBIT(8) - EORBIT(9)) / 2;
            EORBIT(2) = (EORBIT(2) - 2 * EORBIT(5) - 2 * EORBIT(6) - EORBIT(9));
        }
    }
    catch (char const *s) {
        error(s);
    }

}


extern "C" void count5(PAIR * const p_edges, int const * const dim_edges, double * const orbits)
{
    try {
        int nn, nn2;
        unordered_map<PAIR, int, hash_PAIR> common2;
        unordered_map<TRIPLE, int, hash_TRIPLE> common3;
        unordered_map<PAIR, int, hash_PAIR>::iterator common2_it;
        unordered_map<TRIPLE, int, hash_TRIPLE>::iterator common3_it;

        GraphData data(p_edges, dim_edges);
        int const * const tri = data.triangles();
        data.common_2_3(common2, common3);

        int const &n = data.n_nodes;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;

        // count complete graphlets on five nodes
        int64 * const C5 = (int64 *)S_alloc(n, sizeof(int64));
        int * const neigh = (int *)R_alloc(n, sizeof(int));
        int * const neigh2 = (int *)R_alloc(n, sizeof(int));
        for (int x = 0; x < n; x++) {
            for (int nx = 0; nx < deg[x]; nx++) {
                int const &y = adj[x][nx];
                if (y >= x)
                    break;
                nn = 0;
                for (int ny = 0; ny < deg[y]; ny++) {
                    int const &z = adj[y][ny];
                    if (z >= y)
                        break;
                    if (data.adjacent(x,z)) {
                        neigh[nn++] = z;
                    }
                }
                for (int i = 0; i < nn; i++) {
                    int const &z = neigh[i];
                    nn2 = 0;
                    for (int j = i + 1; j < nn; j++) {
                        int const &zz = neigh[j];
                        if (data.adjacent(z,zz)) {
                            neigh2[nn2++] = zz;
                        }
                    }
                    for (int i2 = 0; i2 < nn2; i2++) {
                        int const &zz = neigh2[i2];
                        for (int j2 = i2 + 1; j2 < nn2; j2++) {
                            int const &zzz = neigh2[j2];
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

        int * const common_x = (int *)S_alloc(n, sizeof(int));
        int * const common_x_list = (int *)R_alloc(n, sizeof(int)), ncx = 0;
        int * const common_a = (int *)S_alloc(n, sizeof(int));
        int * const common_a_list = (int *)R_alloc(n, sizeof(int)), nca = 0;

        // set up a system of equations relating orbit counts
        for (int x = 0; x < n; x++) {
            for (int i = 0; i < ncx; i++) {
                common_x[common_x_list[i]] = 0;
            }
            ncx = 0;

            // smaller graphlets
            ORBIT(0) = deg[x];
            for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                int const &a = adj[x][nx1];
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &b = adj[x][nx2];
                    if (data.adjacent(a, b))
                        ORBIT(3)++;
                    else
                        ORBIT(2)++;
                }
                for (int na = 0; na < deg[a]; na++) {
                    int const &b = adj[a][na];
                    if (b != x && !data.adjacent(x, b)) {
                        ORBIT(1)++;
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
                int const &a = inc[x][nx1].first, &xa = inc[x][nx1].second;

                for (int i = 0; i < nca; i++)
                    common_a[common_a_list[i]] = 0;
                nca = 0;
                for (int na = 0;na < deg[a]; na++) {
                    int const &b = adj[a][na];
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
                    int const &b = inc[x][nx2].first, &xb = inc[x][nx2].second;
                    if (!data.adjacent(a,b))
                        continue;
                    for (int nx3 = nx2+1; nx3 < deg[x]; nx3++) {
                        int const &c = inc[x][nx3].first, &xc = inc[x][nx3].second;
                        if (!data.adjacent(a, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(14)++;
                        f_70 += common3_get(TRIPLE(a, b, c)) - 1; // o_{70}+4o_{72}
                        f_71 += (tri[xa] > 2 && tri[xb] > 2) ? common3_get(TRIPLE(x, a, b)) - 1 : 0; // 2o_{71}+12o_{72}
                        f_71 += (tri[xa] > 2 && tri[xc] > 2) ? common3_get(TRIPLE(x, a, c)) - 1 : 0;
                        f_71 += (tri[xb] > 2 && tri[xc] > 2) ? common3_get(TRIPLE(x, b, c)) - 1 : 0;
                        f_67 += tri[xa] - 2 + tri[xb] - 2 + tri[xc] - 2; // o_{67}+12o_{72}+4o_{71}
                        f_66 += common2_get(PAIR(a, b)) - 2; // o_{66}+12o_{72}+2o_{71}+3o_{70}
                        f_66 += common2_get(PAIR(a, c)) - 2;
                        f_66 += common2_get(PAIR(b, c)) - 2;
                        f_58 += deg[x] - 3; // o_{58}+4o_{72}+2o_{71}+o_{67}
                        f_57 += deg[a] - 3 + deg[b] - 3 + deg[c] - 3; // o_{57}+12o_{72}+4o_{71}+3o_{70}+o_{67}+2o_{66}
                    }
                }

                // x = orbit-13 (diamond)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first, &xb = inc[x][nx2].second;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nx3 = nx2 + 1; nx3 < deg[x]; nx3++) {
                        int const &c = inc[x][nx3].first, &xc = inc[x][nx3].second;
                        if (!data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(13)++;
                        f_69 += (tri[xb] > 1 && tri[xc] > 1) ? common3_get(TRIPLE(x, b, c)) - 1 : 0; // 4o_{69}+2o_{71}
                        f_68 += common3_get(TRIPLE(a, b, c)) - 1; // o_{68}+2o_{71}
                        f_64 += common2_get(PAIR(b, c)) - 2; // o_{64}+2o_{71}+4o_{69}+o_{68}
                        f_61 += tri[xb] - 1 + tri[xc] - 1; // 2o_{61}+4o_{71}+8o_{69}+2o_{67}
                        f_60 += common2_get(PAIR(a, b)) - 1; // o_{60}+4o_{71}+2o_{68}+2o_{67}
                        f_60 += common2_get(PAIR(a, c)) - 1;
                        f_55 += tri[xa] - 2; // 3o_{55}+2o_{71}+2o_{67}
                        f_48 += deg[b] - 2 + deg[c] - 2; // o_{48}+4o_{71}+8o_{69}+2o_{68}+2o_{67}+2o_{64}+2o_{61}+o_{60}
                        f_42 += deg[x] - 3; // o_{42}+2o_{71}+4o_{69}+2o_{67}+2o_{61}+3o_{55}
                        f_41 += deg[a] - 3; // o_{41}+2o_{71}+o_{68}+2o_{67}+o_{60}+3o_{55}
                    }
                }

                // x = orbit-12 (diamond)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int const &c = inc[a][na].first, &ac = inc[a][na].second;
                        if ((c == x) || data.adjacent(x, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(12)++;
                        f_65 += (tri[ac] > 1) ? common3_get(TRIPLE(a, b, c)) : 0; // 2o_{65}+3o_{70}
                        f_63 += common_x[c] - 2; // o_{63}+3o_{70}+2o_{68}
                        f_59 += tri[ac] - 1 + common2_get(PAIR(b, c)) - 1; // o_{59}+6o_{70}+2o_{68}+4o_{65}
                        f_54 += common2_get(PAIR(a, b)) - 2; // 2o_{54}+3o_{70}+o_{66}+2o_{65}
                        f_47 += deg[x] - 2; // o_{47}+3o_{70}+2o_{68}+o_{66}+o_{63}+o_{60}
                        f_46 += deg[c] - 2; // o_{46}+3o_{70}+2o_{68}+2o_{65}+o_{63}+o_{59}
                        f_40 += deg[a] - 3 + deg[b] - 3; // o_{40}+6o_{70}+2o_{68}+2o_{66}+4o_{65}+o_{60}+o_{59}+4o_{54}
                    }
                }

                // x = orbit-8 (cycle)
                for (int nx2  =nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first, &xb = inc[x][nx2].second;
                    if (data.adjacent(a, b))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int const &c = inc[a][na].first, &ac = inc[a][na].second;
                        if ((c == x) || data.adjacent(x, c) || !data.adjacent(b, c))
                            continue;
                        ORBIT(8)++;
                        f_62 += (tri[ac] > 0) ? common3_get(TRIPLE(a, b, c)) : 0; // 2o_{62}+o_{68}
                        f_53 += tri[xa] + tri[xb]; // o_{53}+2o_{68}+2o_{64}+2o_{63}
                        f_51 += tri[ac] + common2_get(PAIR(c, b)); // o_{51}+2o_{68}+2o_{63}+4o_{62}
                        f_50 += common_x[c] - 2; // 3o_{50}+o_{68}+2o_{63}
                        f_49 += common_a[b] - 2; // 2o_{49}+o_{68}+o_{64}+2o_{62}
                        f_38 += deg[x] - 2; // o_{38}+o_{68}+o_{64}+2o_{63}+o_{53}+3o_{50}
                        f_37 += deg[a] - 2 + deg[b] - 2; // o_{37}+2o_{68}+2o_{64}+2o_{63}+4o_{62}+o_{53}+o_{51}+4o_{49}
                        f_36 += deg[c] - 2; // o_{36}+o_{68}+2o_{63}+2o_{62}+o_{51}+3o_{50}
                    }
                }

                // x = orbit-11 (paw)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nx3 = 0; nx3 < deg[x]; nx3++) {
                        int const &c = inc[x][nx3].first, &xc = inc[x][nx3].second;
                        if ((c == a) || (c==b) || data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(11)++;
                        f_44 += tri[xc]; // 4o_{44}+o_{67}+2o_{61}
                        f_33 += deg[x] - 3; // 2o_{33}+o_{67}+2o_{61}+3o_{58}+4o_{44}+2o_{42}
                        f_30 += deg[c] - 1; // o_{30}+o_{67}+o_{63}+2o_{61}+o_{53}+4o_{44}
                        f_26 += deg[a] - 2 + deg[b] - 2; // o_{26}+2o_{67}+2o_{63}+2o_{61}+6o_{58}+o_{53}+2o_{47}+2o_{42}
                    }
                }

                // x = orbit-10 (paw)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first;
                    if (!data.adjacent(a, b))
                        continue;
                    for (int nb = 0; nb < deg[b]; nb++) {
                        int const &c = inc[b][nb].first, &bc = inc[b][nb].second;
                        if ((c == x) || (c == a) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(10)++;
                        f_52 += common_a[c] - 1; // 2o_{52}+2o_{66}+2o_{64}+o_{59}
                        f_43 += tri[bc]; // 2o_{43}+2o_{66}+o_{60}+o_{59}
                        f_32 += deg[b] - 3; // 2o_{32}+2o_{66}+o_{60}+o_{59}+2o_{57}+2o_{43}+2o_{41}+o_{40}
                        f_29 += deg[c] - 1; // o_{29}+2o_{66}+2o_{64}+o_{60}+o_{59}+o_{53}+2o_{52}+2o_{43}
                        f_25 += deg[a] - 2; // 2o_{25}+2o_{66}+2o_{64}+o_{59}+2o_{57}+2o_{52}+o_{48}+o_{40}
                    }
                }

                // x = orbit-9 (paw)
                for (int na1 = 0; na1 < deg[a]; na1++) {
                    int const &b = inc[a][na1].first, &ab = inc[a][na1].second;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int na2 = na1 + 1; na2 < deg[a]; na2++) {
                        int const &c = inc[a][na2].first, &ac = inc[a][na2].second;
                        if ((c == x) || !data.adjacent(b, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(9)++;
                        f_56 += (tri[ab] > 1 && tri[ac] > 1) ? common3_get(TRIPLE(a, b, c)) : 0; // 3o_{56}+2o_{65}
                        f_45 += common2_get(PAIR(b, c)) - 1; // o_{45}+2o_{65}+2o_{62}+3o_{56}
                        f_39 += tri[ab] - 1 + tri[ac] - 1; // 2o_{39}+4o_{65}+o_{59}+6o_{56}
                        f_31 += deg[a] - 3; // o_{31}+2o_{65}+o_{59}+3o_{56}+o_{43}+2o_{39}
                        f_28 += deg[x] - 1; // o_{28}+2o_{65}+2o_{62}+o_{59}+o_{51}+o_{43}
                        f_24 += deg[b] - 2 + deg[c] - 2; // o_{24}+4o_{65}+4o_{62}+o_{59}+6o_{56}+o_{51}+2o_{45}+2o_{39}
                    }
                }

                // x = orbit-4 (path)
                for (int na = 0; na < deg[a]; na++) {
                    int const &b = inc[a][na].first;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int nb = 0;nb < deg[b]; nb++) {
                        int const &c = inc[b][nb].first, &bc = inc[b][nb].second;
                        if ((c == a) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(4)++;
                        f_35 += common_a[c] - 1; // 2o_{35}+o_{59}+2o_{52}+2o_{45}
                        f_34 += common_x[c]; // 2o_{34}+o_{59}+2o_{52}+o_{51}
                        f_27 += tri[bc]; // 2o_{27}+o_{59}+o_{51}+2o_{45}
                        f_18 += deg[b] - 2; // 2o_{18}+o_{59}+o_{51}+2o_{46}+2o_{45}+2o_{36}+2o_{27}+o_{24}
                        f_16 += deg[x] - 1; // o_{16}+o_{59}+2o_{52}+o_{51}+2o_{46}+2o_{36}+2o_{34}+o_{29}
                        f_15 += deg[c] - 1; // o_{15}+o_{59}+2o_{52}+o_{51}+2o_{45}+2o_{35}+2o_{34}+2o_{27}
                    }
                }

                // x = orbit-5 (path)
                for (int nx2 = 0; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first;
                    if ((b==a) || data.adjacent(a, b))
                        continue;
                    for (int nb = 0; nb < deg[b]; nb++) {
                        int const &c = inc[b][nb].first;
                        if ((c == x) || data.adjacent(a, c) || data.adjacent(x, c))
                            continue;
                        ORBIT(5)++;
                        f_17 += deg[a] - 1; // 2o_{17}+o_{60}+o_{53}+o_{51}+o_{48}+o_{37}+2o_{34}+2o_{30}
                    }
                }

                // x = orbit-6 (claw)
                for (int na1 = 0;na1 < deg[a]; na1++) {
                    int const &b = inc[a][na1].first;
                    if ((b == x) || data.adjacent(x, b))
                        continue;
                    for (int na2 = na1 + 1; na2 < deg[a]; na2++) {
                        int const &c = inc[a][na2].first;
                        if ((c == x) || data.adjacent(x,c) || data.adjacent(b,c))
                            continue;
                        ORBIT(6)++;
                        f_22 += deg[a] - 3; // 3o_{22}+2o_{54}+o_{40}+o_{39}+o_{32}+2o_{31}
                        f_20 += deg[x] - 1; // o_{20}+2o_{54}+2o_{49}+o_{40}+o_{37}+o_{32}
                        f_19 += deg[b] - 1 + deg[c] - 1; // o_{19}+4o_{54}+4o_{49}+o_{40}+2o_{39}+o_{37}+2o_{35}+2o_{31}
                    }
                }

                // x = orbit-7 (claw)
                for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                    int const &b = inc[x][nx2].first;
                    if (data.adjacent(a, b))
                        continue;
                    for (int nx3 = nx2 + 1; nx3 < deg[x]; nx3++) {
                        int const &c = inc[x][nx3].first;
                        if (data.adjacent(a, c) || data.adjacent(b, c))
                            continue;
                        ORBIT(7)++;
                        f_23 += deg[x] - 3; // 4o_{23}+o_{55}+o_{42}+2o_{33}
                        f_21 += deg[a] - 1 + deg[b] - 1 + deg[c] - 1; // o_{21}+3o_{55}+3o_{50}+2o_{42}+2o_{38}+2o_{33}
                    }
                }
            }

            // solve equations
            ORBIT(72) = C5[x];
            ORBIT(71) = (f_71 - 12 * ORBIT(72)) / 2;
            ORBIT(70) = (f_70 - 4 * ORBIT(72));
            ORBIT(69) = (f_69 - 2 * ORBIT(71))/4;
            ORBIT(68) = (f_68 - 2 * ORBIT(71));
            ORBIT(67) = (f_67 - 12 * ORBIT(72) - 4 * ORBIT(71));
            ORBIT(66) = (f_66 - 12 * ORBIT(72) - 2 * ORBIT(71) - 3 * ORBIT(70));
            ORBIT(65) = (f_65 - 3 * ORBIT(70)) / 2;
            ORBIT(64) = (f_64 - 2 * ORBIT(71) - 4 * ORBIT(69) - 1 * ORBIT(68));
            ORBIT(63) = (f_63 - 3 * ORBIT(70) - 2 * ORBIT(68));
            ORBIT(62) = (f_62 - 1 * ORBIT(68)) / 2;
            ORBIT(61) = (f_61 - 4 * ORBIT(71) - 8 * ORBIT(69) - 2 * ORBIT(67)) / 2;
            ORBIT(60) = (f_60 - 4 * ORBIT(71) - 2 * ORBIT(68) - 2 * ORBIT(67));
            ORBIT(59) = (f_59 - 6 * ORBIT(70) - 2 * ORBIT(68) - 4 * ORBIT(65));
            ORBIT(58) = (f_58 - 4 * ORBIT(72) - 2 * ORBIT(71) - 1 * ORBIT(67));
            ORBIT(57) = (f_57 - 12 * ORBIT(72) - 4 * ORBIT(71) - 3 * ORBIT(70) - 1 * ORBIT(67) - 2 * ORBIT(66));
            ORBIT(56) = (f_56 - 2 * ORBIT(65)) / 3;
            ORBIT(55) = (f_55 - 2 * ORBIT(71) - 2 * ORBIT(67)) / 3;
            ORBIT(54) = (f_54 - 3 * ORBIT(70) - 1 * ORBIT(66) - 2 * ORBIT(65)) / 2;
            ORBIT(53) = (f_53 - 2 * ORBIT(68) - 2 * ORBIT(64) - 2 * ORBIT(63));
            ORBIT(52) = (f_52 - 2 * ORBIT(66) - 2 * ORBIT(64) - 1 * ORBIT(59)) / 2;
            ORBIT(51) = (f_51 - 2 * ORBIT(68) - 2 * ORBIT(63) - 4 * ORBIT(62));
            ORBIT(50) = (f_50 - 1 * ORBIT(68) - 2 * ORBIT(63)) / 3;
            ORBIT(49) = (f_49 - 1 * ORBIT(68) - 1 * ORBIT(64) - 2 * ORBIT(62)) / 2;
            ORBIT(48) = (f_48 - 4 * ORBIT(71) - 8 * ORBIT(69) - 2 * ORBIT(68) - 2 * ORBIT(67) - 2 * ORBIT(64) - 2 * ORBIT(61) - 1 * ORBIT(60));
            ORBIT(47) = (f_47 - 3 * ORBIT(70) - 2 * ORBIT(68) - 1 * ORBIT(66) - 1 * ORBIT(63) - 1 * ORBIT(60));
            ORBIT(46) = (f_46 - 3 * ORBIT(70) - 2 * ORBIT(68) - 2 * ORBIT(65) - 1 * ORBIT(63) - 1 * ORBIT(59));
            ORBIT(45) = (f_45 - 2 * ORBIT(65) - 2 * ORBIT(62) - 3 * ORBIT(56));
            ORBIT(44) = (f_44 - 1 * ORBIT(67) - 2 * ORBIT(61))/4;
            ORBIT(43) = (f_43 - 2 * ORBIT(66) - 1 * ORBIT(60) - 1 * ORBIT(59)) / 2;
            ORBIT(42) = (f_42 - 2 * ORBIT(71) - 4 * ORBIT(69) - 2 * ORBIT(67) - 2 * ORBIT(61) - 3 * ORBIT(55));
            ORBIT(41) = (f_41 - 2 * ORBIT(71) - 1 * ORBIT(68) - 2 * ORBIT(67) - 1 * ORBIT(60) - 3 * ORBIT(55));
            ORBIT(40) = (f_40 - 6 * ORBIT(70) - 2 * ORBIT(68) - 2 * ORBIT(66) - 4 * ORBIT(65) - 1 * ORBIT(60) - 1 * ORBIT(59) - 4 * ORBIT(54));
            ORBIT(39) = (f_39 - 4 * ORBIT(65) - 1 * ORBIT(59) - 6 * ORBIT(56)) / 2;
            ORBIT(38) = (f_38 - 1 * ORBIT(68) - 1 * ORBIT(64) - 2 * ORBIT(63) - 1 * ORBIT(53) - 3 * ORBIT(50));
            ORBIT(37) = (f_37 - 2 * ORBIT(68) - 2 * ORBIT(64) - 2 * ORBIT(63) - 4 * ORBIT(62) - 1 * ORBIT(53) - 1 * ORBIT(51) - 4 * ORBIT(49));
            ORBIT(36) = (f_36 - 1 * ORBIT(68) - 2 * ORBIT(63) - 2 * ORBIT(62) - 1 * ORBIT(51) - 3 * ORBIT(50));
            ORBIT(35) = (f_35 - 1 * ORBIT(59) - 2 * ORBIT(52) - 2 * ORBIT(45)) / 2;
            ORBIT(34) = (f_34 - 1 * ORBIT(59) - 2 * ORBIT(52) - 1 * ORBIT(51)) / 2;
            ORBIT(33) = (f_33 - 1 * ORBIT(67) - 2 * ORBIT(61) - 3 * ORBIT(58) - 4 * ORBIT(44) - 2 * ORBIT(42)) / 2;
            ORBIT(32) = (f_32 - 2 * ORBIT(66) - 1 * ORBIT(60) - 1 * ORBIT(59) - 2 * ORBIT(57) - 2 * ORBIT(43) - 2 * ORBIT(41) - 1 * ORBIT(40)) / 2;
            ORBIT(31) = (f_31 - 2 * ORBIT(65) - 1 * ORBIT(59) - 3 * ORBIT(56) - 1 * ORBIT(43) - 2 * ORBIT(39));
            ORBIT(30) = (f_30 - 1 * ORBIT(67) - 1 * ORBIT(63) - 2 * ORBIT(61) - 1 * ORBIT(53) - 4 * ORBIT(44));
            ORBIT(29) = (f_29 - 2 * ORBIT(66) - 2 * ORBIT(64) - 1 * ORBIT(60) - 1 * ORBIT(59) - 1 * ORBIT(53) - 2 * ORBIT(52) - 2 * ORBIT(43));
            ORBIT(28) = (f_28 - 2 * ORBIT(65) - 2 * ORBIT(62) - 1 * ORBIT(59) - 1 * ORBIT(51) - 1 * ORBIT(43));
            ORBIT(27) = (f_27 - 1 * ORBIT(59) - 1 * ORBIT(51) - 2 * ORBIT(45)) / 2;
            ORBIT(26) = (f_26 - 2 * ORBIT(67) - 2 * ORBIT(63) - 2 * ORBIT(61) - 6 * ORBIT(58) - 1 * ORBIT(53) - 2 * ORBIT(47) - 2 * ORBIT(42));
            ORBIT(25) = (f_25 - 2 * ORBIT(66) - 2 * ORBIT(64) - 1 * ORBIT(59) - 2 * ORBIT(57) - 2 * ORBIT(52) - 1 * ORBIT(48) - 1 * ORBIT(40)) / 2;
            ORBIT(24) = (f_24 - 4 * ORBIT(65) - 4 * ORBIT(62) - 1 * ORBIT(59) - 6 * ORBIT(56) - 1 * ORBIT(51) - 2 * ORBIT(45) - 2 * ORBIT(39));
            ORBIT(23) = (f_23 - 1 * ORBIT(55) - 1 * ORBIT(42) - 2 * ORBIT(33))/4;
            ORBIT(22) = (f_22 - 2 * ORBIT(54) - 1 * ORBIT(40) - 1 * ORBIT(39) - 1 * ORBIT(32) - 2 * ORBIT(31)) / 3;
            ORBIT(21) = (f_21 - 3 * ORBIT(55) - 3 * ORBIT(50) - 2 * ORBIT(42) - 2 * ORBIT(38) - 2 * ORBIT(33));
            ORBIT(20) = (f_20 - 2 * ORBIT(54) - 2 * ORBIT(49) - 1 * ORBIT(40) - 1 * ORBIT(37) - 1 * ORBIT(32));
            ORBIT(19) = (f_19 - 4 * ORBIT(54) - 4 * ORBIT(49) - 1 * ORBIT(40) - 2 * ORBIT(39) - 1 * ORBIT(37) - 2 * ORBIT(35) - 2 * ORBIT(31));
            ORBIT(18) = (f_18 - 1 * ORBIT(59) - 1 * ORBIT(51) - 2 * ORBIT(46) - 2 * ORBIT(45) - 2 * ORBIT(36) - 2 * ORBIT(27) - 1 * ORBIT(24)) / 2;
            ORBIT(17) = (f_17 - 1 * ORBIT(60) - 1 * ORBIT(53) - 1 * ORBIT(51) - 1 * ORBIT(48) - 1 * ORBIT(37) - 2 * ORBIT(34) - 2 * ORBIT(30)) / 2;
            ORBIT(16) = (f_16 - 1 * ORBIT(59) - 2 * ORBIT(52) - 1 * ORBIT(51) - 2 * ORBIT(46) - 2 * ORBIT(36) - 2 * ORBIT(34) - 1 * ORBIT(29));
            ORBIT(15) = (f_15 - 1 * ORBIT(59) - 2 * ORBIT(52) - 1 * ORBIT(51) - 2 * ORBIT(45) - 2 * ORBIT(35) - 2 * ORBIT(34) - 2 * ORBIT(27));
        }
    }
    catch (char const *s) {
        error(s);
    }
}


/** count edge orbits of graphlets on max 5 nodes */

 extern "C" void ecount5(PAIR * const p_edges, int const * const dim_edges, double * const orbits) {
    try {
        unordered_map<PAIR, int, hash_PAIR> common2;
        unordered_map<TRIPLE, int, hash_TRIPLE> common3;
        unordered_map<PAIR, int, hash_PAIR>::iterator common2_it;
        unordered_map<TRIPLE, int, hash_TRIPLE>::iterator common3_it;

        GraphData data(p_edges, dim_edges);
        int const * const tri = data.triangles();
        data.common_2_3(common2, common3);

        int const &n = data.n_nodes;
        int const &m = data.n_edges;
        int const *const deg = data.deg;
        int const *const *const adj = data.adj;
        PII const *const *const inc = data.inc;

        // count complete graphlets on five nodes
        int64 * const C5 = (int64 *)S_alloc(m,sizeof(int64));
        int * const neighx = (int *)R_alloc(n, sizeof(int)); // lookup table - edges to neighbors of x
        memset(neighx , -1, n * sizeof(int));
        int * const neigh = (int *)R_alloc(n, sizeof(int)), nn; // lookup table - common neighbors of x and y
        PII * const neigh_edges = (PII *)R_alloc(n, sizeof(PII)); // list of common neighbors of x and y
        int * const neigh2 = (int *)R_alloc(n, sizeof(int)), nn2;
        TIII *const neigh2_edges = (TIII *)R_alloc(n, sizeof(TIII));
        for (int x = 0; x < n; x++) {
            for (int nx = 0; nx < deg[x]; nx++) {
                int y = inc[x][nx].first, xy = inc[x][nx].second;
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
                for (int i = 0 ; i < nn; i++) {
                    int const &z = neigh[i], &xz = neigh_edges[i].first, &yz = neigh_edges[i].second;
                    nn2 = 0;
                    for (int j = i + 1; j < nn; j++) {
                        int const &w = neigh[j], &xw = neigh_edges[j].first, &yw = neigh_edges[j].second;
                        if (data.adjacent(z, w)) {
                            neigh2[nn2] = w;
                            int const &zw = data.getEdgeId(z,w);
                            neigh2_edges[nn2] = TIII(xw, yw, zw);
                            nn2++;
                        }
                    }
                    for (int i2 = 0; i2 < nn2; i2++) {
                        int const &z2 = neigh2[i2];
                        int const &z2x = neigh2_edges[i2].first;
                        int const &z2y = neigh2_edges[i2].second;
                        int const &z2z = neigh2_edges[i2].third;
                        for (int j2 = i2 + 1; j2 < nn2; j2++) {
                            int const &z3 = neigh2[j2];
                            int const &z3x = neigh2_edges[j2].first;
                            int const &z3y = neigh2_edges[j2].second;
                            int const &z3z = neigh2_edges[j2].third;
                            if (data.adjacent(z2, z3)) {
                                int const &zid = data.getEdgeId(z2, z3);
                                C5[xy]++;  C5[xz]++;  C5[yz]++;
                                C5[z2x]++; C5[z2y]++; C5[z2z]++;
                                C5[z3x]++; C5[z3y]++; C5[z3z]++;
                                C5[zid]++;
                            }
                        }
                    }
                }
            }
            for (int nx = 0; nx < deg[x]; nx++) {
                int const &y = inc[x][nx].first;
                neighx[y] = -1;
            }
        }

        // set up a system of equations relating orbits for every node
        int * const common_x = (int *)S_alloc(n,sizeof(int));
        int * const common_x_list = (int *)R_alloc(n, sizeof(int)), nc_x = 0;
        int * const common_y = (int *)S_alloc(n, sizeof(int));
        int * const common_y_list = (int *)R_alloc(n, sizeof(int)), nc_y = 0;

        for (int x = 0; x < n; x++) {
            // common nodes of x and some other node
            for (int i = 0; i < nc_x; i++)
                common_x[common_x_list[i]] = 0;
            nc_x = 0;
            for (int nx = 0; nx < deg[x]; nx++) {
                int const &a = adj[x][nx];
                for (int na = 0; na < deg[a]; na++) {
                    int const &z = adj[a][na];
                    if (z == x)
                        continue;
                    if (common_x[z] == 0)
                        common_x_list[nc_x++] = z;
                    common_x[z]++;
                }
            }
            for (int nx = 0; nx < deg[x]; nx++) {
                int const &y = inc[x][nx].first, &xy = inc[x][nx].second;
                int const &e = xy;
                if (y >= x)
                    break;

                // common nodes of y and some other node
                for (int i = 0; i < nc_y; i++)
                    common_y[common_y_list[i]] = 0;
                nc_y = 0;
                for (int ny = 0; ny < deg[y]; ny++) {
                    int const &a = adj[y][ny];
                    for (int na = 0; na < deg[a]; na++) {
                        int const &z = adj[a][na];
                        if (z == y)
                            continue;
                        if (common_y[z] == 0)
                            common_y_list[nc_y++] = z;
                        common_y[z]++;
                    }
                }

                int64 f_66 = 0, f_65 = 0, f_62 = 0, f_61 = 0, f_60 = 0, f_51 = 0, f_50 = 0; // 11
                int64 f_64 = 0, f_58 = 0, f_55 = 0, f_48 = 0, f_41 = 0, f_35 = 0; // 10
                int64 f_63 = 0, f_59 = 0, f_57 = 0, f_54 = 0, f_53 = 0, f_52 = 0, f_47 = 0, f_40 = 0, f_39 = 0, f_34 = 0, f_33 = 0; // 9
                int64 f_45 = 0, f_36 = 0, f_26 = 0, f_23 = 0, f_19 = 0; // 7
                int64 f_49 = 0, f_38 = 0, f_37 = 0, f_32 = 0, f_25 = 0, f_22 = 0, f_18 = 0; // 6
                int64 f_56 = 0, f_46 = 0, f_44 = 0, f_43 = 0, f_42 = 0, f_31 = 0, f_30 = 0; // 5
                int64 f_27 = 0, f_17 = 0, f_15 = 0; // 4
                int64 f_20 = 0, f_16 = 0, f_13 = 0; // 3
                int64 f_29 = 0, f_28 = 0, f_24 = 0, f_21 = 0, f_14 = 0, f_12 = 0; // 2

                // smaller (3-node) graphlets
                for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                    int const &z = adj[x][nx1];
                    if (z == y)
                        continue;
                    if (data.adjacent(y, z))
                        EORBIT(1)++;
                    else
                        EORBIT(0)++;
                }
                for (int ny = 0;ny < deg[y]; ny++) {
                    int const &z = adj[y][ny];
                    if (z == x)
                        continue;
                    if (!data.adjacent(x, z))
                        EORBIT(0)++;
                }

                // edge-orbit 11 = (14,14)
                for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                    int const &a = adj[x][nx1], &xa = inc[x][nx1].second;
                    if (a == y || !data.adjacent(y, a))
                        continue;
                    for (int nx2 = nx1+1; nx2 < deg[x]; nx2++) {
                        int const &b = adj[x][nx2], &xb = inc[x][nx2].second;
                        if (b == y || !data.adjacent(y, b) || !data.adjacent(a, b))
                            continue;
                        int const &ya = data.getEdgeId(y,a), &yb = data.getEdgeId(y,b), &ab = data.getEdgeId(a,b);
                        EORBIT(11)++;
                        f_66 += common3_get(TRIPLE(x, y, a)) - 1; // 2e_{66}+6e_{67}
                        f_66 += common3_get(TRIPLE(x, y, b)) - 1;
                        f_65 += common3_get(TRIPLE(a, b, x)) - 1; // e_{65}+6e_{67}
                        f_65 += common3_get(TRIPLE(a, b, y)) - 1;
                        f_62 += tri[xy] - 2; // e_{62}+2e_{66}+3e_{67}
                        f_61 += (tri[xa] - 2) + (tri[xb] - 2) + (tri[ya] - 2) + (tri[yb] - 2); // e_{61}+2e_{65}+4e_{66}+12e_{67}
                        f_60 += tri[ab] - 2; // e_{60}+e_{65}+3e_{67}
                        f_51 += (deg[x]  -3) + (deg[y] - 3); // e_{51}+e_{61}+2e_{62}+e_{65}+4e_{66}+6e_{67}
                        f_50 += (deg[a] - 3) + (deg[b] - 3); // e_{50}+2e_{60}+e_{61}+2e_{65}+2e_{66}+6e_{67}
                    }
                }

                // edge-orbit 10 = (13,13)
                for (int nx1 = 0;nx1 < deg[x]; nx1++) {
                    int const &a = adj[x][nx1], &xa = inc[x][nx1].second;
                    if (a == y || !data.adjacent(y, a))
                        continue;
                    for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                        int const &b = adj[x][nx2], &xb = inc[x][nx2].second;
                        if (b == y || !data.adjacent(y, b) || data.adjacent(a, b))
                            continue;
                        int const &ya = data.getEdgeId(y, a), &yb = data.getEdgeId(y, b);
                        EORBIT(10)++;
                        f_64 += common3_get(TRIPLE(a, b, x)) - 1; // e_{64}+2e_{66}
                        f_64 += common3_get(TRIPLE(a, b, y)) - 1;
                        f_58 += common2_get(PAIR(a, b)) - 2; // e_{58}+e_{64}+e_{66}
                        f_55 += (tri[xa] - 1) + (tri[xb] - 1) + (tri[ya] - 1) + (tri[yb] - 1); // e_{55}+4e_{62}+2e_{64}+4e_{66}
                        f_48 += tri[xy] - 2; // 3e_{48}+2e_{62}+e_{66}
                        f_41 += (deg[a] - 2) + (deg[b] - 2); // e_{41}+e_{55}+2e_{58}+2e_{62}+2e_{64}+2e_{66}
                        f_35 += (deg[x] - 3) + (deg[y] - 3); // e_{35}+6e_{48}+e_{55}+4e_{62}+e_{64}+2e_{66}
                    }
                }

                // edge-orbit 9 = (12,13)
                for (int nx = 0; nx < deg[x]; nx++) {
                    int const &a = adj[x][nx], &xa = inc[x][nx].second;
                    if (a == y)
                        continue;
                    for (int ny = 0; ny < deg[y]; ny++) {
                        int const &b = adj[y][ny], &yb = inc[y][ny].second;
                        if (b == x || !data.adjacent(a, b))
                            continue;
                        int const &adj_ya = data.adjacent(y,a), &adj_xb = data.adjacent(x,b);
                        if (adj_ya + adj_xb != 1)
                            continue;
                        int ab = data.getEdgeId(a,b);
                        EORBIT(9)++;
                        if (adj_xb) {
                            int const &xb = data.getEdgeId(x, b);
                            f_63 += common3_get(TRIPLE(a, b, y)) - 1; // 2e_{63}+2e_{65}
                            f_59 += common3_get(TRIPLE(a, b, x)); // 2e_{59}+2e_{65}
                            f_57 += common_y[a] - 2; // e_{57}+2e_{63}+2e_{64}+2e_{65}
                            f_54 += tri[yb] - 1; // 2e_{54}+e_{61}+2e_{63}+2e_{65}
                            f_53 += tri[xa] - 1; // e_{53}+2e_{59}+2e_{64}+2e_{65}
                            f_47 += tri[xb] - 2; // 2e_{47}+2e_{59}+e_{61}+2e_{65}
                            f_40 += deg[y] - 2; // e_{40}+2e_{54}+e_{55}+e_{57}+e_{61}+2e_{63}+2e_{64}+2e_{65}
                            f_39 += deg[a] - 2; // e_{39}+e_{52}+e_{53}+e_{57}+2e_{59}+2e_{63}+2e_{64}+2e_{65}
                            f_34 += deg[x] - 3; // e_{34}+2e_{47}+e_{53}+e_{55}+2e_{59}+e_{61}+2e_{64}+2e_{65}
                            f_33 += deg[b] - 3; // e_{33}+2e_{47}+e_{52}+2e_{54}+2e_{59}+e_{61}+2e_{63}+2e_{65}
                        } else if (adj_ya) {
                            int const &ya = data.getEdgeId(y, a);
                            f_63 += common3_get(TRIPLE(a, b, x)) - 1;
                            f_59 += common3_get(TRIPLE(a, b, y));
                            f_57 += common_x[b] - 2;
                            f_54 += tri[xa] - 1;
                            f_53 += tri[yb] - 1;
                            f_47 += tri[ya] - 2;
                            f_40 += deg[x] - 2;
                            f_39 += deg[b] - 2;
                            f_34 += deg[y] - 3;
                            f_33 += deg[a] - 3;
                        }
                        f_52 += tri[ab] - 1; // e_{52}+2e_{59}+2e_{63}+2e_{65}
                    }
                }

                // edge-orbit 8 = (10,11)
                for (int nx = 0; nx < deg[x]; nx++) {
                    int const &a = adj[x][nx];
                    if (a == y || !data.adjacent(y,a))
                        continue;
                    for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                        int const &b = adj[x][nx1];
                        if (b == y || b == a || data.adjacent(y, b) || data.adjacent(a, b))
                            continue;
                        EORBIT(8)++;
                    }
                    for (int ny1 = 0; ny1 < deg[y]; ny1++) {
                        int const &b = adj[y][ny1];
                        if (b == x || b == a || data.adjacent(x, b) || data.adjacent(a, b))
                            continue;
                        EORBIT(8)++;
                    }
                }

                // edge-orbit 7 = (10,10)
                for (int nx = 0;nx < deg[x]; nx++) {
                    int const &a = adj[x][nx];
                    if (a == y || !data.adjacent(y, a))
                        continue;
                    for (int na = 0;na < deg[a]; na++) {
                        int const &b = adj[a][na], &ab = inc[a][na].second;
                        if (b == x || b == y || data.adjacent(x, b) || data.adjacent(y, b))
                            continue;
                        EORBIT(7)++;
                        f_45 += common_x[b] - 1; // e_{45}+e_{52}+4e_{58}+4e_{60}
                        f_45 += common_y[b] - 1;
                        f_36 += tri[ab]; // 2e_{36}+e_{52}+2e_{60}
                        f_26 += deg[a] - 3; // 2e_{26}+e_{33}+2e_{36}+e_{50}+e_{52}+2e_{60}
                        f_23 += deg[b] - 1; // e_{23}+2e_{36}+e_{45}+e_{52}+2e_{58}+2e_{60}
                        f_19 += (deg[x] - 2) + (deg[y] - 2); // e_{19}+e_{33}+2e_{41}+e_{45}+2e_{50}+e_{52}+4e_{58}+4e_{60}
                    }
                }

                // edge-orbit 6 = (9,11)
                for (int ny1 = 0;ny1 < deg[y]; ny1++) {
                    int const &a = adj[y][ny1], &ya = inc[y][ny1].second;
                    if (a == x || data.adjacent(x, a))
                        continue;
                    for (int ny2 = ny1 + 1; ny2 < deg[y]; ny2++) {
                        int b = adj[y][ny2], yb = inc[y][ny2].second;
                        if (b == x || data.adjacent(x, b) || !data.adjacent(a,b))
                            continue;
                        int const &ab = data.getEdgeId(a, b);
                        EORBIT(6)++;
                        f_49 += common3_get(TRIPLE(y, a, b)); // 3e_{49}+e_{59}
                        f_38 += tri[ab] - 1; // e_{38}+3e_{49}+e_{56}+e_{59}
                        f_37 += tri[xy]; // e_{37}+e_{53}+e_{59}
                        f_32 += (tri[ya] - 1) + (tri[yb] - 1); // 2e_{32}+6e_{49}+e_{53}+2e_{59}
                        f_25 += deg[y] - 3; // e_{25}+2e_{32}+e_{37}+3e_{49}+e_{53}+e_{59}
                        f_22 += deg[x] - 1; // e_{22}+e_{37}+e_{44}+e_{53}+e_{56}+e_{59}
                        f_18 += (deg[a] - 2) + (deg[b] - 2); // e_{18}+2e_{32}+2e_{38}+e_{44}+6e_{49}+e_{53}+2e_{56}+2e_{59}
                    }
                }
                for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                    int const &a = adj[x][nx1], &xa = inc[x][nx1].second;
                    if (a == y || data.adjacent(y, a))
                        continue;
                    for (int nx2 = nx1 + 1; nx2 < deg[x]; nx2++) {
                        int b = adj[x][nx2], xb = inc[x][nx2].second;
                        if (b == y || data.adjacent(y, b) || !data.adjacent(a, b))
                            continue;
                        int const &ab = data.getEdgeId(a, b);
                        EORBIT(6)++;
                        f_49 += common3_get(TRIPLE(x, a, b));
                        f_38 += tri[ab] - 1;
                        f_37 += tri[xy];
                        f_32 += (tri[xa] - 1) + (tri[xb] - 1);
                        f_25 += deg[x] - 3;
                        f_22 += deg[y] - 1;
                        f_18 += (deg[a] - 2) + (deg[b] - 2);
                    }
                }

                // edge-orbit 5 = (8,8)
                for (int nx = 0;nx < deg[x]; nx++) {
                    int const &a = adj[x][nx], &xa = inc[x][nx].second;
                    if (a == y || data.adjacent(y, a))
                        continue;
                    for (int ny = 0; ny < deg[y]; ny++) {
                        int const &b = adj[y][ny], yb = inc[y][ny].second;
                        if (b == x || data.adjacent(x, b) || !data.adjacent(a, b))
                            continue;
                        int const &ab = data.getEdgeId(a, b);
                        EORBIT(5)++;
                        f_56 += common3_get(TRIPLE(x, a, b)); // 2e_{56}+2e_{63}
                        f_56 += common3_get(TRIPLE(y, a, b));
                        f_46 += tri[xy]; // e_{46}+e_{57}+e_{63}
                        f_44 += tri[xa] + tri[yb]; // e_{44}+2e_{56}+e_{57}+2e_{63}
                        f_43 += tri[ab]; // e_{43}+2e_{56}+e_{63}
                        f_42 += common_x[b] - 2; // 2e_{42}+2e_{56}+e_{57}+2e_{63}
                        f_42 += common_y[a] - 2;
                        f_31 += (deg[x] - 2) + (deg[y] - 2); // e_{31}+2e_{42}+e_{44}+2e_{46}+2e_{56}+2e_{57}+2e_{63}
                        f_30 += (deg[a] - 2) + (deg[b] - 2); // e_{30}+2e_{42}+2e_{43}+e_{44}+4e_{56}+e_{57}+2e_{63}
                    }
                }

                // edge-orbit 4 = (6,7)
                for (int ny1 = 0; ny1 < deg[y]; ny1++) {
                    int const &a = adj[y][ny1];
                    if (a == x || data.adjacent(x, a))
                        continue;
                    for (int ny2 = ny1 + 1; ny2 < deg[y]; ny2++) {
                        int const &b = adj[y][ny2];
                        if (b == x || data.adjacent(x, b) || data.adjacent(a, b))
                            continue;
                        EORBIT(4)++;
                        f_27 += tri[xy]; // e_{27}+e_{34}+e_{47}
                        f_17 += deg[y] - 3; // 3e_{17}+2e_{25}+e_{27}+e_{32}+e_{34}+e_{47}
                        f_15 += (deg[a] - 1) + (deg[b] - 1); // e_{15}+2e_{25}+2e_{29}+e_{31}+2e_{32}+e_{34}+2e_{42}+2e_{47}
                    }
                }
                for (int nx1 = 0; nx1 < deg[x]; nx1++) {
                    int const &a = adj[x][nx1];
                    if (a == y || data.adjacent(y, a))
                        continue;
                    for (int nx2 = nx1+1; nx2<deg[x]; nx2++) {
                        int const &b = adj[x][nx2];
                        if (b == y || data.adjacent(y,b) || data.adjacent(a,b))
                            continue;
                        EORBIT(4)++;
                        f_27 += tri[xy];
                        f_17 += deg[x] - 3;
                        f_15 += (deg[a] - 1) + (deg[b] - 1);
                    }
                }

                // edge-orbit 3 = (5,5)
                for (int nx = 0; nx < deg[x]; nx++) {
                    int const &a = adj[x][nx];
                    if (a == y || data.adjacent(y, a))
                        continue;
                    for (int ny = 0; ny < deg[y]; ny++) {
                        int const &b = adj[y][ny];
                        if (b == x || data.adjacent(x,b) || data.adjacent(a,b))
                            continue;
                        EORBIT(3)++;
                        f_20 += tri[xy]; // e_{20}+e_{40}+e_{54}
                        f_16 += (deg[x] - 2) + (deg[y] - 2); // 2e_{16}+2e_{20}+2e_{22}+e_{31}+2e_{40}+e_{44}+2e_{54}
                        f_13 += (deg[a] - 1) + (deg[b] - 1); // e_{13}+2e_{22}+2e_{28}+e_{31}+e_{40}+2e_{44}+2e_{54}
                    }
                }

                // edge-orbit 2 = (4,5)
                for (int ny = 0; ny < deg[y]; ny++) {
                    int const &a = adj[y][ny];
                    if (a == x || data.adjacent(x, a))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int const &b = adj[a][na], &ab = inc[a][na].second;
                        if (b == y || data.adjacent(y,b) || data.adjacent(x,b))
                            continue;
                        EORBIT(2)++;
                        f_29 += common_y[b] - 1; // 2e_{29}+2e_{38}+e_{45}+e_{52}
                        f_28 += common_x[b]; // 2e_{28}+2e_{43}+e_{45}+e_{52}
                        f_24 += tri[xy]; // e_{24}+e_{39}+e_{45}+e_{52}
                        f_21 += tri[ab]; // 2e_{21}+2e_{38}+2e_{43}+e_{52}
                        f_14 += deg[a] - 2; // 2e_{14}+e_{18}+2e_{21}+e_{30}+2e_{38}+e_{39}+2e_{43}+e_{52}
                        f_12 += deg[b] - 1; // e_{12}+2e_{21}+2e_{28}+2e_{29}+2e_{38}+2e_{43}+e_{45}+e_{52}
                    }
                }
                for (int nx = 0;nx<deg[x];nx++) {
                    int const &a = adj[x][nx];
                    if (a == y || data.adjacent(y, a))
                        continue;
                    for (int na = 0; na < deg[a]; na++) {
                        int const &b = adj[a][na], &ab = inc[a][na].second;
                        if (b == x || data.adjacent(x, b) || data.adjacent(y, b))
                            continue;
                        EORBIT(2)++;
                        f_29 += common_x[b] - 1;
                        f_28 += common_y[b];
                        f_24 += tri[xy];
                        f_21 += tri[ab];
                        f_14 += deg[a] - 2;
                        f_12 += deg[b] - 1;
                    }
                }

                // solve system of equations
                EORBIT(67) = C5[e];
                EORBIT(66) = (f_66 - 6 * EORBIT(67)) / 2;
                EORBIT(65) = (f_65 - 6 * EORBIT(67));
                EORBIT(64) = (f_64 - 2 * EORBIT(66));
                EORBIT(63) = (f_63 - 2 * EORBIT(65)) / 2;
                EORBIT(62) = (f_62 - 2 * EORBIT(66) - 3 * EORBIT(67));
                EORBIT(61) = (f_61 - 2 * EORBIT(65) - 4 * EORBIT(66) - 12 * EORBIT(67));
                EORBIT(60) = (f_60 - 1 * EORBIT(65) - 3 * EORBIT(67));
                EORBIT(59) = (f_59 - 2 * EORBIT(65)) / 2;
                EORBIT(58) = (f_58 - 1 * EORBIT(64) - 1 * EORBIT(66));
                EORBIT(57) = (f_57 - 2 * EORBIT(63) - 2 * EORBIT(64) - 2 * EORBIT(65));
                EORBIT(56) = (f_56 - 2 * EORBIT(63)) / 2;
                EORBIT(55) = (f_55 - 4 * EORBIT(62) - 2 * EORBIT(64) - 4 * EORBIT(66));
                EORBIT(54) = (f_54 - 1 * EORBIT(61) - 2 * EORBIT(63) - 2 * EORBIT(65)) / 2;
                EORBIT(53) = (f_53 - 2 * EORBIT(59) - 2 * EORBIT(64) - 2 * EORBIT(65));
                EORBIT(52) = (f_52 - 2 * EORBIT(59) - 2 * EORBIT(63) - 2 * EORBIT(65));
                EORBIT(51) = (f_51 - 1 * EORBIT(61) - 2 * EORBIT(62) - 1 * EORBIT(65) - 4 * EORBIT(66) - 6 * EORBIT(67));
                EORBIT(50) = (f_50 - 2 * EORBIT(60) - 1 * EORBIT(61) - 2 * EORBIT(65) - 2 * EORBIT(66) - 6 * EORBIT(67));
                EORBIT(49) = (f_49 - 1 * EORBIT(59)) / 3;
                EORBIT(48) = (f_48 - 2 * EORBIT(62) - 1 * EORBIT(66)) / 3;
                EORBIT(47) = (f_47 - 2 * EORBIT(59) - 1 * EORBIT(61) - 2 * EORBIT(65)) / 2;
                EORBIT(46) = (f_46 - 1 * EORBIT(57) - 1 * EORBIT(63));
                EORBIT(45) = (f_45 - 1 * EORBIT(52) - 4 * EORBIT(58) - 4 * EORBIT(60));
                EORBIT(44) = (f_44 - 2 * EORBIT(56) - 1 * EORBIT(57) - 2 * EORBIT(63));
                EORBIT(43) = (f_43 - 2 * EORBIT(56) - 1 * EORBIT(63));
                EORBIT(42) = (f_42 - 2 * EORBIT(56) - 1 * EORBIT(57) - 2 * EORBIT(63)) / 2;
                EORBIT(41) = (f_41 - 1 * EORBIT(55) - 2 * EORBIT(58) - 2 * EORBIT(62) - 2 * EORBIT(64) - 2 * EORBIT(66));
                EORBIT(40) = (f_40 - 2 * EORBIT(54) - 1 * EORBIT(55) - 1 * EORBIT(57) - 1 * EORBIT(61) - 2 * EORBIT(63) - 2 * EORBIT(64) - 2 * EORBIT(65));
                EORBIT(39) = (f_39 - 1 * EORBIT(52) - 1 * EORBIT(53) - 1 * EORBIT(57) - 2 * EORBIT(59) - 2 * EORBIT(63) - 2 * EORBIT(64) - 2 * EORBIT(65));
                EORBIT(38) = (f_38 - 3 * EORBIT(49) - 1 * EORBIT(56) - 1 * EORBIT(59));
                EORBIT(37) = (f_37 - 1 * EORBIT(53) - 1 * EORBIT(59));
                EORBIT(36) = (f_36 - 1 * EORBIT(52) - 2 * EORBIT(60)) / 2;
                EORBIT(35) = (f_35 - 6 * EORBIT(48) - 1 * EORBIT(55) - 4 * EORBIT(62) - 1 * EORBIT(64) - 2 * EORBIT(66));
                EORBIT(34) = (f_34 - 2 * EORBIT(47) - 1 * EORBIT(53) - 1 * EORBIT(55) - 2 * EORBIT(59) - 1 * EORBIT(61) - 2 * EORBIT(64) - 2 * EORBIT(65));
                EORBIT(33) = (f_33 - 2 * EORBIT(47) - 1 * EORBIT(52) - 2 * EORBIT(54) - 2 * EORBIT(59) - 1 * EORBIT(61) - 2 * EORBIT(63) - 2 * EORBIT(65));
                EORBIT(32) = (f_32 - 6 * EORBIT(49) - 1 * EORBIT(53) - 2 * EORBIT(59)) / 2;
                EORBIT(31) = (f_31 - 2 * EORBIT(42) - 1 * EORBIT(44) - 2 * EORBIT(46) - 2 * EORBIT(56) - 2 * EORBIT(57) - 2 * EORBIT(63));
                EORBIT(30) = (f_30 - 2 * EORBIT(42) - 2 * EORBIT(43) - 1 * EORBIT(44) - 4 * EORBIT(56) - 1 * EORBIT(57) - 2 * EORBIT(63));
                EORBIT(29) = (f_29 - 2 * EORBIT(38) - 1 * EORBIT(45) - 1 * EORBIT(52)) / 2;
                EORBIT(28) = (f_28 - 2 * EORBIT(43) - 1 * EORBIT(45) - 1 * EORBIT(52)) / 2;
                EORBIT(27) = (f_27 - 1 * EORBIT(34) - 1 * EORBIT(47));
                EORBIT(26) = (f_26 - 1 * EORBIT(33) - 2 * EORBIT(36) - 1 * EORBIT(50) - 1 * EORBIT(52) - 2 * EORBIT(60)) / 2;
                EORBIT(25) = (f_25 - 2 * EORBIT(32) - 1 * EORBIT(37) - 3 * EORBIT(49) - 1 * EORBIT(53) - 1 * EORBIT(59));
                EORBIT(24) = (f_24 - 1 * EORBIT(39) - 1 * EORBIT(45) - 1 * EORBIT(52));
                EORBIT(23) = (f_23 - 2 * EORBIT(36) - 1 * EORBIT(45) - 1 * EORBIT(52) - 2 * EORBIT(58) - 2 * EORBIT(60));
                EORBIT(22) = (f_22 - 1 * EORBIT(37) - 1 * EORBIT(44) - 1 * EORBIT(53) - 1 * EORBIT(56) - 1 * EORBIT(59));
                EORBIT(21) = (f_21 - 2 * EORBIT(38) - 2 * EORBIT(43) - 1 * EORBIT(52)) / 2;
                EORBIT(20) = (f_20 - 1 * EORBIT(40) - 1 * EORBIT(54));
                EORBIT(19) = (f_19 - 1 * EORBIT(33) - 2 * EORBIT(41) - 1 * EORBIT(45) - 2 * EORBIT(50) - 1 * EORBIT(52) - 4 * EORBIT(58) - 4 * EORBIT(60));
                EORBIT(18) = (f_18 - 2 * EORBIT(32) - 2 * EORBIT(38) - 1 * EORBIT(44) - 6 * EORBIT(49) - 1 * EORBIT(53) - 2 * EORBIT(56) - 2 * EORBIT(59));
                EORBIT(17) = (f_17 - 2 * EORBIT(25) - 1 * EORBIT(27) - 1 * EORBIT(32) - 1 * EORBIT(34) - 1 * EORBIT(47)) / 3;
                EORBIT(16) = (f_16 - 2 * EORBIT(20) - 2 * EORBIT(22) - 1 * EORBIT(31) - 2 * EORBIT(40) - 1 * EORBIT(44) - 2 * EORBIT(54)) / 2;
                EORBIT(15) = (f_15 - 2 * EORBIT(25) - 2 * EORBIT(29) - 1 * EORBIT(31) - 2 * EORBIT(32) - 1 * EORBIT(34) - 2 * EORBIT(42) - 2 * EORBIT(47));
                EORBIT(14) = (f_14 - 1 * EORBIT(18) - 2 * EORBIT(21) - 1 * EORBIT(30) - 2 * EORBIT(38) - 1 * EORBIT(39) - 2 * EORBIT(43) - 1 * EORBIT(52)) / 2;
                EORBIT(13) = (f_13 - 2 * EORBIT(22) - 2 * EORBIT(28) - 1 * EORBIT(31) - 1 * EORBIT(40) - 2 * EORBIT(44) - 2 * EORBIT(54));
                EORBIT(12) = (f_12 - 2 * EORBIT(21) - 2 * EORBIT(28) - 2 * EORBIT(29) - 2 * EORBIT(38) - 2 * EORBIT(43) - 1 * EORBIT(45) - 1 * EORBIT(52));
            }
        }
    }
    catch (char const *s) {
        error(s);
    }

}
