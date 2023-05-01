#include <bits/stdc++.h>
using namespace std;

mt19937 rng(chrono::high_resolution_clock::now().time_since_epoch().count());

vector<int> generate(int n) {
	vector<int> ans;
	for (int i = 0; i < n; i++)
		ans.push_back(i);
	shuffle(ans.begin(), ans.end(), rng);
	return ans;
}

bool check(vector<int> a, vector<int> b, vector<int> ops) {
	for (auto i : ops) {
		swap(a[i], a[a[i]]);
		swap(b[i], b[b[i]]);
	}

	bool both_sorted = true;
	for (int i = 0; i < a.size(); i++)
		both_sorted &= (a[i] == i && b[i] == i);
	return both_sorted;
}

vector<vector<int>> game_permutation(vector<int> &actual_a,
                                     vector<int> &actual_b) {
	vector<vector<int>> ans;
	for (int i = 0; i < actual_a.size(); i++)
		if (actual_a[i] != i || actual_b[i] != i)
			ans.push_back({i, actual_a[i], actual_b[i]});
	return ans;
}

void swap(vector<int> &actual_a, vector<int> &actual_b, vector<int> &pos) {
	swap(actual_a[pos[0]], actual_a[pos[1]]);
	swap(actual_b[pos[0]], actual_b[pos[2]]);
}

int min_count; // Le asignamos un valor lo suficientemente grande, como 2n.
vector<int> indices, indices_aux;

void brute_force(vector<int> &actual_a, vector<int> &actual_b) {
	int n = actual_a.size();

	bool both_sorted = true;
	for (int i = 0; i < n; i++)
		both_sorted &= (actual_a[i] == i && actual_b[i] == i);

	if (both_sorted) {
		if (indices_aux.size() < min_count) {
			min_count = indices_aux.size();
			indices = indices_aux;
		}
		return;
	}

	vector<vector<int>> g_perm = game_permutation(actual_a, actual_b);

	for (int i = 0; i < g_perm.size(); i++) {
		swap(actual_a, actual_b, g_perm[i]);
		indices_aux.push_back(g_perm[i][0]);
		brute_force(actual_a, actual_b);
		indices_aux.pop_back();
		swap(actual_a, actual_b, g_perm[i]);
	}
}

template <typename T> struct dinic {
	struct edge {
		int src, dst;
		T low, cap, flow;
		int rev;
	};

	int n;
	vector<vector<edge>> adj;

	dinic(int n) : n(n), adj(n + 2) {}

	void add_edge(int src, int dst, T low, T cap) {
		adj[src].push_back({src, dst, low, cap, 0, (int)adj[dst].size()});
		if (src == dst)
			adj[src].back().rev++;
		adj[dst].push_back({dst, src, 0, 0, 0, (int)adj[src].size() - 1});
	}

	vector<int> level, iter;

	T augment(int u, int t, T cur) {
		if (u == t)
			return cur;
		for (int &i = iter[u]; i < (int)adj[u].size(); ++i) {
			edge &e = adj[u][i];
			if (e.cap - e.flow > 0 && level[u] > level[e.dst]) {
				T f = augment(e.dst, t, min(cur, e.cap - e.flow));
				if (f > 0) {
					e.flow += f;
					adj[e.dst][e.rev].flow -= f;
					return f;
				}
			}
		}
		return 0;
	}

	int bfs(int s, int t) {
		level.assign(n + 2, n + 2);
		level[t] = 0;
		queue<int> Q;
		for (Q.push(t); !Q.empty(); Q.pop()) {
			int u = Q.front();
			if (u == s)
				break;
			for (edge &e : adj[u]) {
				edge &erev = adj[e.dst][e.rev];
				if (erev.cap - erev.flow > 0 && level[e.dst] > level[u] + 1) {
					Q.push(e.dst);
					level[e.dst] = level[u] + 1;
				}
			}
		}
		return level[s];
	}

	const T oo = numeric_limits<T>::max();

	T max_flow(int source, int sink) {
		vector<T> delta(n + 2);

		for (int u = 0; u < n; ++u) // initialize
			for (auto &e : adj[u]) {
				delta[e.src] -= e.low;
				delta[e.dst] += e.low;
				e.cap -= e.low;
				e.flow = 0;
			}

		T sum = 0;
		int s = n, t = n + 1;

		for (int u = 0; u < n; ++u) {
			if (delta[u] > 0) {
				add_edge(s, u, 0, delta[u]);
				sum += delta[u];
			} else if (delta[u] < 0)
				add_edge(u, t, 0, -delta[u]);
		}

		add_edge(sink, source, 0, oo);
		T flow = 0;

		while (bfs(s, t) < n + 2) {
			iter.assign(n + 2, 0);
			for (T f; (f = augment(s, t, oo)) > 0;)
				flow += f;
		}

		if (flow != sum)
			return -1; // no solution

		for (int u = 0; u < n; ++u)
			for (auto &e : adj[u]) {
				e.cap += e.low;
				e.flow += e.low;
				edge &erev = adj[e.dst][e.rev];
				erev.cap -= e.low;
				erev.flow -= e.low;
			}

		adj[sink].pop_back();
		adj[source].pop_back();

		while (bfs(source, sink) < n + 2) {
			iter.assign(n + 2, 0);
			for (T f; (f = augment(source, sink, oo)) > 0;)
				flow += f;
		} // level[u] == n + 2 ==> s-side

		return flow;
	}
};

void map_cycles(vector<int> &a, vector<int> &b, vector<int> &cca,
                vector<int> &ccb, vector<int> &sz, vector<vector<int>> &cycles,
                int &cc) {
	int n = a.size();
	for (int i = 0; i < n; i++) {
		if (cca[i])
			continue;
		int act = i;
		while (!cca[act]) {
			cca[act] = cc;
			cycles[cc].push_back(act);
			sz[cc]++;
			act = a[act];
		}
		cc++;
	}

	for (int i = 0; i < n; i++) {
		if (ccb[i])
			continue;
		int act = i;
		while (!ccb[act]) {
			ccb[act] = cc;
			cycles[cc].push_back(act);
			sz[cc]++;
			act = b[act];
		}
		cc++;
	}
}

typedef pair<int, int> pii;

vector<int> exists_solution(vector<int> &cca, vector<int> &ccb, vector<int> &sz,
                            int cc, int len) {
	dinic<int> g(cc + 2);
	int source = 0, sink = cc, source_t = cc + 1;
	int n = cca.size();

	// limitamos la cantidad de flujo que se va a pasar por len, este len es la
	// longitud de la secuencia de operaciones que se quiere chequear si existe
	// o no solucion
	g.add_edge(source_t, source, 0, len);

	vector<int> added_edge_for_cc(cc);
	map<pii, int> common_spot;
	int max_cca = 1;
	for (int i = 0; i < n; i++) {
		max_cca = max(max_cca, cca[i]);

		if (!added_edge_for_cc[cca[i]]) {
			g.add_edge(source, cca[i], sz[cca[i]] - 1, 2 * n);
			added_edge_for_cc[cca[i]] = 1;
		}
		if (!added_edge_for_cc[ccb[i]]) {
			g.add_edge(ccb[i], sink, sz[ccb[i]] - 1, 2 * n);
			added_edge_for_cc[ccb[i]] = 1;
		}

		if (common_spot[pii(cca[i], ccb[i])])
			continue;
		common_spot[pii(cca[i], ccb[i])] = i + 1;
		g.add_edge(cca[i], ccb[i], 0, 2 * n);
	}

	if (g.max_flow(source_t, sink) == -1)
		return {};

	vector<int> ans(n);
	for (int i = 1; i <= max_cca; i++)
		for (auto e : g.adj[i])
			if (e.dst > max_cca && e.dst < cc)
				ans[common_spot[pii(i, e.dst)] - 1] = e.flow;

	return ans;
}

vector<int> find_suitable_freqs(vector<int> &cca, vector<int> &ccb,
                                vector<int> &sz, int cc) {
	// Usemos busqueda binaria para hallar la longitud minima de una secuencia
	// terminal

	int p2n = 1, sol_len = -1, n = cca.size();
	while (p2n <= n)
		p2n <<= 1;
	for (; p2n; p2n >>= 1)
		if (exists_solution(cca, ccb, sz, cc, sol_len + p2n).size() == 0)
			sol_len += p2n;
	sol_len++;

	return exists_solution(cca, ccb, sz, cc, sol_len);
}

pii dfs(int u, vector<vector<pii>> &g, vector<bool> &mk, vector<pii> &parent) {
	mk[u] = 1;
	for (auto e : g[u]) {
		int v = e.first;
		int pos = e.second;
		if (mk[v]) {
			if (v != parent[u].first)
				return pii(u, pos);
			continue;
		}

		parent[v] = pii(u, pos);
		pii x = dfs(v, g, mk, parent);
		if (x != pii(-1, -1))
			return x;
	}
	return pii(-1, -1);
}

void remove_cycles(vector<int> &cca, vector<int> &ccb, vector<int> &freqs,
                   int cc) {
	bool found_cycle = 0;
	int n = cca.size();
	do {

		vector<vector<pii>> g(cc);
		vector<bool> mk(cc);
		vector<pii> parent(cc);

		for (int i = 0; i < n; i++) {
			if (freqs[i]) {
				g[cca[i]].push_back(pii(ccb[i], i));
				g[ccb[i]].push_back(pii(cca[i], i));
			}
		}

		found_cycle = 0;
		for (int i = 1; i < cc; i++) {
			if (mk[i])
				continue;
			parent[i] = pii(-1, -1);
			pii back_edge = dfs(i, g, mk, parent);

			if (back_edge == pii(-1, -1))
				continue;

			found_cycle = 1;
			int target_parent =
			    cca[back_edge.second] + ccb[back_edge.second] - back_edge.first;

			vector<pii> cycle;
			cycle.push_back(back_edge);

			int act = back_edge.first;
			while (act != target_parent) {
				cycle.push_back(parent[act]);
				act = parent[act].first;
			}

			int min_pos = 0;
			for (int j = 0; j < cycle.size(); j++)
				if (freqs[cycle[j].second] < freqs[cycle[min_pos].second])
					min_pos = j;

			for (int j = 0; j < cycle.size(); j++) {
				if (j == min_pos)
					continue;
				if ((j & 1) != (min_pos & 1))
					freqs[cycle[j].second] += freqs[cycle[min_pos].second];
				else
					freqs[cycle[j].second] -= freqs[cycle[min_pos].second];
			}
			freqs[cycle[min_pos].second] = 0;

			break;
		}
	} while (found_cycle);
}

vector<vector<int>> build_relative_solutions(vector<int> &freqs,
                                             vector<vector<int>> &cycles,
                                             int cc) {
	vector<vector<int>> ans(cc);

	for (int i = 1; i < cc; i++) {
		int sum = 0, cycle_sz = cycles[i].size();
		for (auto p : cycles[i])
			sum += freqs[p];

		assert(sum >= cycle_sz - 1);

		int act = 0;
		vector<int> cycle = cycles[i];
		vector<int> freqs_cpy = freqs;
		while (cycle.size() > 1) {
			int to_do = -1;
			for (int p = 0; p < cycle.size(); p++) {
				if (freqs_cpy[cycle[p]] &&
				    !freqs_cpy[cycle[(p + 1) % cycle.size()]])
					to_do = p;
			}
			if (to_do == -1)
				to_do = 0;

			ans[i].push_back(cycle[to_do]);
			freqs_cpy[cycle[to_do]]--;

			vector<int> n_cycle;
			for (int p = 0; p < cycle.size(); p++)
				if (p != (to_do + 1) % cycle.size())
					n_cycle.push_back(cycle[p]);

			cycle = n_cycle;
		}

		for (auto x : cycles[i])
			for (int j = 0; j < freqs_cpy[x]; j++)
				ans[i].push_back(x);
	}

	return ans;
}

vector<int> find_super_seq(vector<vector<int>> &relative_solutions, int n) {
#define all(v) (v).begin(), (v).end()

	int cc = relative_solutions.size();
	vector<vector<int>> times_back(n);
	queue<int> able_to_do;

	for (int i = 1; i < cc; i++) {
		reverse(all(relative_solutions[i]));

		if (relative_solutions[i].empty())
			continue;

		times_back[relative_solutions[i].back()].push_back(i);
		if (times_back[relative_solutions[i].back()].size() == 2)
			able_to_do.push(relative_solutions[i].back());
	}

	vector<int> ans;
	while (!able_to_do.empty()) {
		int p = able_to_do.front();
		able_to_do.pop();

		ans.push_back(p);
		int c0 = times_back[p][0];
		int c1 = times_back[p][1];
		times_back[p].clear();

		relative_solutions[c0].pop_back();
		relative_solutions[c1].pop_back();

		if (!relative_solutions[c0].empty()) {
			times_back[relative_solutions[c0].back()].push_back(c0);
			if (times_back[relative_solutions[c0].back()].size() == 2)
				able_to_do.push(relative_solutions[c0].back());
		}

		if (!relative_solutions[c1].empty()) {
			times_back[relative_solutions[c1].back()].push_back(c1);
			if (times_back[relative_solutions[c1].back()].size() == 2)
				able_to_do.push(relative_solutions[c1].back());
		}
	}

	return ans;
}

vector<int> solve(vector<int> &a, vector<int> &b) {
	int n = a.size();

	// Mapeemos los ciclos en a y b en cca y ccb, y sus longitudes en sz.
	int cc = 1;
	vector<int> cca(n), ccb(n), sz(2 * n + 5);
	vector<vector<int>> cycles(2 * n + 5);
	map_cycles(a, b, cca, ccb, sz, cycles, cc);

	// Se tienen una lista de frecuencias que no tiene por que cumplir que el
	// grafo bipartito asociado sea un bosque

	vector<int> freqs = find_suitable_freqs(cca, ccb, sz, cc);

	// Usemos el algoritmo visto para modificar la lista de frecuencias de forma
	// tal que el grafo bipartito asociado sea un bosque

	remove_cycles(cca, ccb, freqs, cc);

	// Con la lista de frecuencias final, solo es necesario encontrar la
	// secuencia respuesta. Para esto, se construye primero una solución para
	// cada ciclo de las permutaciones y a partir de este se halla la respuesta
	// final

	vector<vector<int>> relative_solutions =
	    build_relative_solutions(freqs, cycles, cc);

	// A partir de las soluciones relativas para cada ciclo se construye la
	// solución final, buscando una secuencia de operaciones que contenga como
	// subsecuencia a todas las secuencias solución halladas para cada ciclo
	// individual

	vector<int> ans = find_super_seq(relative_solutions, n);

	return ans;
}

int main() {

	cout << "Seleccione el modo de prueba:\n";
	cout << "1 - Comprueba fuerza bruta vs solución propuesta.\n";
	cout << "2 - Comprueba que la solución propuesta genera una secuencia "
	        "terminal e imprime los valores generados y la secuencia de "
	        "operaciones solución.\n";

	int mode;
	cin >> mode;

	int n, tc, debug = 1;
	cout << "Tamaño de las permutaciones a probar:\n";
	cin >> n;
	cout << "Número de casos de prueba a probar:\n";
	cin >> tc;
	if (mode == 1) {
		cout << "Imprimir las permutaciones iniciales y las secuencias "
		        "generadas "
		        "por la fuerza bruta y la solución propuesta? (0-1)\n";
		cin >> debug;
	}

	for (int i = 0; i < tc; i++) {
		vector<int> a = generate(n);
		vector<int> b = generate(n);

		vector<int> sol = solve(a, b);
		vector<int> sol_bf;

		if (mode == 1) {
			min_count = 2 * n;
			indices = {};
			indices_aux = {};
			brute_force(a, b);
			sol_bf = indices;
		}

		if (debug) {
			cout << "\nTest " << i + 1 << ':' << '\n';

			cout << "a:                           ";
			for (auto x : a)
				cout << ' ' << x + 1;
			cout << '\n';

			cout << "b:                           ";
			for (auto x : b)
				cout << ' ' << x + 1;
			cout << '\n';

			if (mode == 1) {
				cout << "respuesta fuerza bruta:      ";
				for (auto x : sol_bf)
					cout << ' ' << x + 1;
				cout << '\n';
			}

			cout << "respuesta solución propuesta:";
			for (auto x : sol)
				cout << ' ' << x + 1;
			cout << '\n';
		}

		if (mode == 1 && !check(a, b, sol_bf)) {
			cout << "En el test " << i + 1
			     << " la fuerza bruta no encontró una respuesta válida.\n";
			continue;
		}
		if (!check(a, b, sol)) {
			cout
			    << "En el test " << i + 1
			    << " la solución propuesta no encontró una respuesta válida.\n";
			continue;
		}

		if (mode == 1 && sol_bf.size() < sol.size()) {
			cout
			    << "En el test " << i + 1
			    << " la respuesta encontrada por la fuerza bruta usó menos "
			       "operaciones que la encontrada por la solución propuesta.\n";
			continue;
		}
		if (mode == 1 && sol_bf.size() > sol.size()) {
			cout
			    << "En el test " << i + 1
			    << " la respuesta encontrada por la solución propuesta usó "
			       "menos operaciones que la encontrada por la fuerza bruta.\n";
			continue;
		}

		// se comprobó lo que se quería

		cout << "Test " << i + 1 << ": ok\n";
		cout << flush;
	}

	return 0;
}
