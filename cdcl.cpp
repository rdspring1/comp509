#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <vector>
#include <list>
#include <unordered_set>
#include <unordered_map>
#include <fstream>
#include <random>
#include <algorithm>
#include <memory>
#include <math.h>
#include <boost/timer/timer.hpp>

using namespace std;

// Heuristic
enum heuristic
{
	MyHeuristic,
	Random
};
const string hstr[] = 
{
	"MyHeuristic", 
	"Random" 
};

enum state
{
	UNIT = -1,
	CONFLICT = 0,
	NONE = 1
};

// Settings
const heuristic h = MyHeuristic;
const int CSIZE = 8;
const int K = 3;
const double LProb = 0.5f;
const double min_LN = 3.0f;
const double max_LN = 6.0f;
const double inc_LN = 0.2f;
const float DECAY = 2.0f;
const float RESTART_INIT = 100;
const float RESTART_CONST = 1.5;
float restart_threshold = 0;
float conflict_count = 0;
int vars = 100;
int backtrack_count = 0;
int added_clauses = 0;

const string FALSE = "False";
const string UNSAT_STR = "UNSAT";
const string VAR = "VARIABLE";
const string TRUTH = "Truth Assignment";
const string COMMENT = "c";
const string PROBLEM = "p";
const string END = "0";
const string cnf_format = "cnf";
const string sat_format = "sat";
const char NEGATION = '-';
const int IGNORE = -1;
const int TRUE = 0;
const int ITER = 100;
const boost::timer::nanosecond_type TIMEOUT(60 * 1000000000LL);
std::default_random_engine generator( (unsigned int)time(NULL) );

typedef std::unordered_map<int, int> wlist;
struct update
{
	int ap;
	int value;
	int parent;

	update(int ap, int value, int parent = IGNORE)
	{
		this->ap = ap;
		this->value = value;
		this->parent = parent;
	}
};

// Implication Graph
vector<int> decision_level;
vector<int> parent;
vector<int> t;
list<int> updates;
list<update> assignment_queue;
unordered_map<int, vector<int>> cnf;
int original_size = 0;

// Two Watched Law - Lazy Data Structure
wlist wl1;
wlist wl2;

// MyHeuristic
vector<float> myh;

void print(vector<int> t)
{
	if(t.size() == 0)
	{
		cout << UNSAT_STR << endl;
	}

	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] != IGNORE)
			cout << VAR << " " << (i+1) << " " << TRUTH << " " <<  bool(t[i]) << endl;
		else
			cout << VAR << " " << (i+1) << " " << TRUTH << " " <<  t[i] << endl;
	}
}

void unit_clause(int literal, int parent = -1)
{
	int value = (literal < 0) ? 0 : 1;
	assignment_queue.push_back(update(abs(literal)-1, value, parent));
}

void preprocess()
{
	for(const auto& c : cnf)
	{
		if(c.second.size() == 1)
		{
			unit_clause(c.second.front());
		}
	}
}

void update_heuristic(const vector<int>& clause)
{
	for(const auto& literal : clause)
	{
		++myh[abs(literal)-1];
	}
}

void setup(heuristic h, bool restart = false)
{
	decision_level.clear();
	decision_level.resize(vars, IGNORE);

	parent.clear();
	parent.resize(vars, IGNORE);

	t.clear();
	t.resize(vars, IGNORE);

	updates.clear();

	if(!restart)
	{
		conflict_count = 0;
		wl1.clear();
		wl2.clear();
		wl1.reserve(cnf.size());
		wl2.reserve(cnf.size());
		for(int i = 0; i < cnf.size(); ++i)
		{
			wl1[i] = 0;
			wl2[i] = cnf[i].size()-1;
		}
		restart_threshold = RESTART_INIT;
	}
	else
	{
		//cout << "Restart" << endl;
		restart_threshold = round(restart_threshold * RESTART_CONST);
	}
	assignment_queue.clear();
	preprocess();

	switch(h)
	{
		case MyHeuristic:
			{
				myh.clear();
				myh.resize(vars, 0);
				for(const auto& clause : cnf)
				{
					update_heuristic(clause.second);
				}
			}
			break;
	}
}

update myh_heuristic(const vector<int>& t)
{
	vector<int> ties;
	float maxValue = 0;
	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] == IGNORE)
		{
			if(myh[i] > maxValue)
			{
				maxValue = myh[i];
				ties.clear();
			}

			if(myh[i] == maxValue)
			{
				ties.push_back(i);
			}
		}
	}
	assert(ties.size() > 0);

	std::uniform_int_distribution<int> p(0,ties.size()-1);
	std::uniform_int_distribution<int> v(0,1);
	return update(ties[p(generator)], v(generator));
}

update random_heuristic(const vector<int>& t)
{
	vector<int> available;
	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] == IGNORE)
		{
			available.push_back(i);
		}
	}
	assert(available.size() > 0);

	std::uniform_int_distribution<int> p(0,available.size()-1);
	std::uniform_int_distribution<int> v(0,1);
	return update(available[p(generator)], v(generator));
}

int evaluate_literal(const int& literal)
{
	int ap = abs(literal)-1;
	if(t[ap] == IGNORE)
	{
		return IGNORE;
	}

	if(literal < 0)
	{
		return (1 - t[ap]);
	}
	return t[ap];
}

state update_watched_literal(bool first, int clause)
{
	//cout << "uwl: " << ((first) ? wl1[clause] : wl2[clause]) << endl;
	int other = (first) ? wl2[clause] : wl1[clause];
	int index = 0;
	state status = NONE;
	int other_literal = IGNORE;
	for(const auto& literal : cnf[clause])
	{
		if(index == other)
		{
			status = (state) evaluate_literal(literal);
			other_literal = literal;
		}
		else if(evaluate_literal(literal) != 0)
		{
			//cout << first << " other: " << other << " clause: " << clause << " index: " << index << endl;
			if(first)
			{
				wl1[clause] = index;
			}
			else
			{
				wl2[clause] = index;
			}
			return NONE;
		}
		++index;
	}

	if(status == UNIT)
	{
		unit_clause(other_literal, clause);
	}
	return status;
}

state evaluate_wlist(const wlist& wl, int& clause_id, bool first)
{
	// Update Watchlist 
	for(const auto& index : wl)
	{
		int literal = cnf[index.first][index.second];
		int truth_value = evaluate_literal(literal);
		if(truth_value == 0)
		{
			state status = update_watched_literal(first, index.first);
			if(status == CONFLICT)
			{
				clause_id = index.first;
				return CONFLICT;
			}
		}
	}
	return NONE;
}

bool update_implication_graph(const int& ap, const int& value, const int& dl, const int& pc)
{
	if(t[ap] != IGNORE)
	{
		return false;
	}

	//cout << dl << " " << (ap+1) << " " << value << " " << pc << endl;
	updates.push_front(ap);
	t[ap] = value;
	decision_level[ap] = dl;
	parent[ap] = pc;
	return true;
}

state unit_propagation(int& clause_id, int dl)
{
	while(!assignment_queue.empty())
	{
		update u = move(assignment_queue.front());
		assignment_queue.pop_front();
		if(!update_implication_graph(u.ap, u.value, dl, u.parent))
		{
			continue;
		}

		state s1 = evaluate_wlist(wl1, clause_id, true);	
		if(s1 == CONFLICT)
		{
			return CONFLICT;
		}

		state s2 = evaluate_wlist(wl2, clause_id, false);
		if(s2 == CONFLICT)
		{
			return CONFLICT;
		}
	}
	return NONE;
}

bool decision_count(const unordered_set<int>& clause, const int& dl)
{
	int sigma = 0;
	int xi = 0;
	for(const auto& literal : clause)
	{
		int ap = abs(literal)-1;
		if(decision_level[ap] == dl)
		{
			if(parent[ap] != IGNORE)
			{
				++xi;
			}
			++sigma;
		}
	}
	// sigma - number of literals in clause at current decision level
	// xi - number of implied literals in clause at current decision level
	//cout << "sigma: " << sigma << " xi: " << xi << endl;
	return (sigma == 1);
}

// Conflict Analysis / New Decision Level
vector<int> analysis(const int& clause_id, int& dl, bool& change, int& UIP)
{
	// Collect all literals from parent clauses - Ignore Duplicates and conflicting variables
	// All literals in unsatisfied clause are false
	unordered_set<int> conflict_set(cnf[clause_id].begin(), cnf[clause_id].end());
	while(!updates.empty() && !decision_count(conflict_set, dl))
	{
		int ap = updates.front();
		int literal = ap+1;
		updates.pop_front();

		//implied literals
		if(decision_level[ap] == dl && parent[ap] != IGNORE)
		{
			//cout << literal << " parent: " << parent[ap] << endl;
			// Resolution Implication Rule
			change = true;
			conflict_set.erase(literal);
			conflict_set.erase(-1 * literal);

			const vector<int>& clause = cnf[parent[ap]];
			for(const int& l : clause)
			{
				if(abs(l) != literal)
				{
					assert(evaluate_literal(l) == 0);
					conflict_set.insert(l);
				}
			}
		}
	}

	// Create Conflict Clause
	int max_dl = -1;
	int new_dl = -1;
	vector<int> conflict_clause;
	for(int literal : conflict_set)
	{
		// All literals in conflict clause are false
		assert(evaluate_literal(literal) == 0);
		conflict_clause.push_back(literal);

		int ap = abs(literal)-1;
		max_dl = max(max_dl, decision_level[ap]);
		if(decision_level[ap] != dl)
		{
			if(decision_level[ap] > new_dl)
			{
				new_dl = decision_level[ap];
			}
		}
		else
		{
			UIP = literal;
		}
	}

	//cout << "dl: " << dl << " max_dl: " << max_dl << " new_dl: " << new_dl << " size: " << conflict_clause.size() << endl;
	if(max_dl <= 0)
	{
		dl = IGNORE;
	}
	else if(new_dl == IGNORE)
	{
		// No Backtrack - Restart
		dl = 0;
	}
	else if(new_dl < dl)
	{
		// Normal Backtrack
		dl = new_dl;
	}

	return conflict_clause;
}

// Update Truth Assignment
void update_truth_assignment(const int& dl)
{
	while(!updates.empty() && decision_level[updates.front()] > dl)
	{
		updates.pop_front();
	}

	for(int ap = 0; ap < t.size(); ++ap)
	{
		if(decision_level[ap] > dl)
		{
			t[ap] = IGNORE;
			decision_level[ap] = IGNORE;
			parent[ap] = IGNORE;
		}
	}
}

bool complete_assignment(const vector<int>& t)
{
	for(int value : t)
	{
		if(value == IGNORE)
		{
			return false;
		}
	}
	return true;
}

// cnf - A formula represented in Conjunctive Normal Form
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(const boost::timer::cpu_timer& timer, heuristic h)
{
	int clause_id = 0;
	int dl = 0;
	if(unit_propagation(clause_id, dl) == CONFLICT)
	{
		return vector<int>();
	}

	while(timer.elapsed().wall < TIMEOUT)
	{
		// Unit Clause Propagation + Check Formula
		switch(unit_propagation(clause_id, dl))
		{
			case CONFLICT:
				{
					++conflict_count;
					bool change = false;
					int UIP = 0;

					// Conflict Analysis / New Decision Level
					vector<int> conflict_clause = analysis(clause_id, dl, change, UIP);
					if(dl < 0)
					{
						return vector<int>();
					}
					++backtrack_count;
					//cout << backtrack_count << endl;
					//cout << "conflict size: " << conflict_clause.size() << " new decision level: " << dl << endl;

					// Update VSIDS Heuristic
					for(int i = 0; i < myh.size(); ++i)
					{
						myh[i] = round(myh[i]/DECAY);
					}
					update_heuristic(conflict_clause);

					// Add Conflict Clause
					if(change)
					{
						wl1[wl1.size()] = 0;
						wl2[wl2.size()] = conflict_clause.size()-1;
						cnf[cnf.size()] = move(conflict_clause);
						++added_clauses;
					}

					// Update Truth Assignment  
					if(conflict_count > restart_threshold || dl == 0)
					{
						setup(h, true);
					}
					else
					{
						update_truth_assignment(dl);
						assignment_queue.clear();
						if(change)
						{
							unit_clause(UIP, cnf.size()-1);
						}
						else
						{
							unit_clause(UIP, clause_id);
						}
					}
				}
				continue;
			case NONE:
				{
					//cout << "NONE" << endl;
					if(complete_assignment(t))
					{
						return t;
					}
				}
		}	

		assignment_queue.clear();
		// Branching Heuristic - Select AP without truth assignment
		switch(h)
		{
			case Random:
				{
					// Random Heuristic
					assignment_queue.push_back(random_heuristic(t));
				}
				break;
			case MyHeuristic:
				{
					// My Heuristic - Variable State Independent Decaying Sum
					assignment_queue.push_back(myh_heuristic(t));
				}
				break;
		}
		++dl;
		++backtrack_count;
	}
	return vector<int>();
}

unordered_map<int, vector<int>> parseCNF(const string& filename)
{
	unordered_map<int, vector<int>> cnf;
	vector<int> clause;
	bool p = false;
	string format;
	int clauses = -1;

	std::ifstream fin(filename);
	std::string line;
	while(std::getline(fin, line) && (!p || cnf.size() < clauses))
	{
		if(!p)
		{
			std::istringstream iss(line);
			string c;
			iss >> c;

			if(c != COMMENT && c == PROBLEM)
			{
				iss >> format >> vars >> clauses;
				p = true;
			}
		}
		else
		{
			std::istringstream iss(line);
			string c;
			while(iss)
			{
				iss >> c;
				if(c == COMMENT)
				{
					break;
				}
				else if(c == END)
				{
					cnf[cnf.size()] = clause;
					clause.clear();
				}
				else
				{
					if(c.size() > 0)
						clause.push_back(atoi(c.c_str()));
				}
				c.clear();
			}
		}
	}
	if(clause.size() > 0)
		cnf[cnf.size()] = clause;

	original_size = cnf.size();
	return cnf;
}

unordered_map<int, vector<int>> randomCNF(const int& N, const double& LProb, const double& LN_Ratio)
{
	std::uniform_int_distribution<int> p(1,N);
	std::uniform_real_distribution<double> l(0.0,1.0);

	int size = int(LN_Ratio * N);
	unordered_map<int, vector<int>> cnf(size);

	for(int n = 0; n < size; ++n)
	{
		vector<int> clause;
		for(int m = 0; m < K; ++m)
		{
			int literal = p(generator);
			if(l(generator) > LProb)
			{
				literal *= -1;
			}
			clause.push_back(literal);
		}
		cnf[n] = move(clause);
	}
	original_size = cnf.size();
	return cnf;
}

void sub(unordered_map<int,vector<int>>& f, const int& ap, const int& value)
{
	for(auto& c : f)
	{
		auto& clause = c.second;
		vector<int> new_clause;
		for(auto& literal : clause)
		{
			bool match = false;
			// evaluate truth value for literal
			bool truth_value = bool(value);

			if(literal == ap)
			{
				match = true;
			}
			else if(literal < 0)
			{
				if(abs(literal) == ap)
				{
					truth_value = !truth_value;
					match = true;
				}
			}

			if(match)
			{
				if(truth_value)
				{
					new_clause.clear();
					new_clause.push_back(TRUE);
					break;
				}
			}
			else
			{
				new_clause.push_back(literal);	
			}
		}
		clause = move(new_clause);
	}
}

bool valid(unordered_map<int, vector<int>> f, const vector<int> t)
{
	if(t.size() == 0)
	{
		return true;
	}

	for(int ap = 0; ap < t.size(); ++ap)
	{
		sub(f, ap+1, t[ap]);
	}
	// check if any clauses are empty: Not Satisfiable under current truth assignment
	// check if all clauses are True: Satisfiable
	for(const auto& c : f)
	{
		auto& clause = c.second;
		// Clause is False, Clause contains multiple propositions, singleton clause
		if(clause.size() != 1 || clause.front() != TRUE)
		{
			cout << c.first << endl;
			return false;
		}
	}
	return true;
}

int main(int argc, char* argv[])
{
	// CNF Format File
	if(argc > 1)
	{
		const string file(argv[1]);
		cnf = parseCNF(file);
		setup(h);
		bool timeout = false;

		// Timer
		std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
		vector<int> result = solve(*timer, h);
		if(timer->elapsed().wall >= TIMEOUT)
		{
			timeout = true;
		}

		print(result); 
		cout << hstr[h] << " Timeout: " << timeout << endl;
		cout << "Number of backtracks: " << backtrack_count << endl;
		cout << "Number of added_clauses: " << added_clauses << endl;
		timer.reset(nullptr);
		assert(valid(cnf, result));
		return 0;
	}

	for(double LN_Ratio = min_LN; LN_Ratio <= max_LN; LN_Ratio += inc_LN)
	{
		cout << "N: " << vars << " L-Probability: " << LProb << " LN_Ratio: " << LN_Ratio << std::endl;         
		int success = 0;
		int timeouts = 0;
		vector<int> added(ITER, 0);
		vector<int> split(ITER, 0);
		vector<double> time(ITER, 0);
		boost::timer::cpu_timer timer;

		// Run benchmark for ITER iterations
		for(int n = 0; n < ITER; ++n)
		{
			cnf = randomCNF(vars, LProb, LN_Ratio);
			setup((heuristic) h);
			bool timeout = false;

			timer.start();
			vector<int> result = solve(timer, (heuristic) h);
			timer.stop();

			if(timer.elapsed().wall >= TIMEOUT)
			{
				timeout = true;
				++timeouts;
			}

			if(result.size() > 0)
			{
				++success;
			}
			assert(valid(cnf, result));

			split[n] = backtrack_count;
			added[n] = added_clauses;
			backtrack_count = 0;
			added_clauses = 0;

			time[n] = atof(timer.format(boost::timer::default_places, "%w").c_str());
			cout << hstr[h] << " - iteration: " << n << " time: " << time[n] << " timeout: " << timeout << std::endl;
		}

		// Sort data and print median value
		cout << hstr[h] << " Success Rate: " << success << " Timeout: " << timeouts << endl;
		std::sort(added.begin(), added.end());
		std::sort(split.begin(), split.end());
		std::sort(time.begin(), time.end());

		cout << "Min number of added clauses: " << added[0] << endl;
		cout << "Median number of added clauses: " << added[ITER/2] << endl;
		cout << "Max number of added clauses: " << added[ITER-1] << endl;

		cout << "Min number of backtracks: " << split[0] << endl;
		cout << "Median number of backtracks: " << split[ITER/2] << endl;
		cout << "Max number of backtracks: " << split[ITER-1] << endl;

		cout << "Min computation time: " << time[0] << endl;
		cout << "Median computation time: " << time[ITER/2] << endl;
		cout << "Max computation time: " << time[ITER-1] << "\n" << endl;
	}
}
