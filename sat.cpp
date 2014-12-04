#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <vector>
#include <list>
#include <stack>
#include <queue>
#include <fstream>
#include <random>
#include <algorithm>
#include <memory>
#include <boost/timer/timer.hpp>

using namespace std;

typedef std::pair<int, int> update;

const string TRUE = "True";
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
const int K = 3;
const int ITER = 100;
const boost::timer::nanosecond_type timeout(60 * 1000000000LL);
std::default_random_engine generator( (unsigned int)time(NULL) );

// Heuristic
enum heuristic
{
	TwoClause,
	Random,
	MyHeuristic,
	Basic 
};
string hstr[] = {"Random", "TwoClause", "MyHeuristic", "Basic"};
const int HEURISTICS = (int) MyHeuristic;

enum state
{
	CONTINUE,
	UNSAT,
	SAT
};
	
// Two Clause Heuristic
vector<int> two_clauses;

int split_count = 0;
int vars = 0;

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

void sub(vector<list<string>>& cnf, const string& ap, const int& value, heuristic h)
{
	/*
	   cout << "sub start: " << cnf.size() << endl;
	   int c = 0;
	   for(const auto& clause : cnf)
	   {
	   cout << "start clause: " << ++c << endl;
	   for(const auto& literal : clause)
	   {
	   cout << "literal: " <<  literal << endl;
	   }
	   }
	   cout << "ap: " << ap << endl;
	   cout << "value: " << value << endl;
	 */

	for(auto& clause : cnf)
	{
		for(auto it = clause.begin(); it != clause.end();)
		{
			auto& literal = *it;
			bool match = false;
			// evaluate truth value for literal
			bool truth_value = bool(value);

			if(literal == ap)
			{
				match = true;
			}
			else if(literal[0] == NEGATION && literal.substr(1) == ap)
			{
				truth_value = !truth_value;
				match = true;
			}

			if(match)
			{
				if(truth_value)
				{
					clause.clear();
					clause.push_back(TRUE);
					break;
				}
				else
				{
					clause.erase(it++);
				}
			}
			else
			{
				++it;
			}
		}

		if(h == TwoClause && clause.size() == 2)
		{
			for(const auto& literal : clause)
			{
				if(literal[0] == NEGATION)
				{
					int value = atoi(literal.substr(1).c_str())-1;
					++two_clauses[value];
					assert(value < two_clauses.size());
					assert(value >= 0);
				}
				else
				{
					int value = atoi(literal.c_str())-1;
					++two_clauses[value];
					assert(value < two_clauses.size());
					assert(value >= 0);
				}
			}
		}
	}

	/*
	   cout << "sub end: " << cnf.size() << endl;
	   int e = 0;
	   for(auto& clause : cnf)
	   {
	   cout << "start clause: " << ++e << endl;
	   for(auto& literal : clause)
	   {
	   cout << "literal: " <<  literal << endl;
	   }
	   }
	 */
}

state valid(const vector<list<string>>& cnf)
{
	// check if any clauses are empty: Not Satisfiable under current truth assignment
	// check if all clauses are True: Satisfiable
	state clause_sat = SAT;
	for(const auto& clause : cnf)
	{
		// Clause is False, Clause contains multiple propositions, singleton clause
		if(clause.size() == 0)
		{
			return UNSAT;
		}
		else if(clause.size() > 1 || clause.front() != TRUE)
		{
			clause_sat = CONTINUE;
		}
	}
	return clause_sat;
}

update two_clause_heuristic(const vector<int>& t)
{
	vector<int> tc;
	tc.reserve(t.size());
	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] == IGNORE)
		{
			tc.push_back(two_clauses[i]);
		}
	}
	assert(tc.size() > 0);

	auto it = max_element(tc.begin(), tc.end());
	vector<int> ties;
	for(int i = 0; i < two_clauses.size(); ++i)
	{
		if(t[i] == IGNORE && two_clauses[i] == *it)
		{
			ties.push_back(i);
		}
	}
	std::uniform_int_distribution<int> p(0,ties.size()-1);
	int max_index = ties[p(generator)];
	two_clauses[max_index] = 0;
	return make_pair(max_index, 0);
}

update random_heuristic(const vector<int>& t)
{
	vector<int> available;
	available.reserve(t.size());
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
	return make_pair(available[p(generator)], v(generator));
}

update basic_heuristic(const vector<int>& t)
{
	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] == IGNORE)
		{
			return make_pair(i, 0);
		}
	}
	assert(true);
}

void unit_propagation(vector<list<string>>& cnf, vector<int>& t, heuristic h)
{
	for(auto& clause : cnf)
	{
		if(clause.size() == 1 && clause.front() != TRUE)
		{
			string literal = clause.front();
			if(literal[0] == NEGATION)
			{
				int ap = atoi(literal.substr(1).c_str())-1;
				assert(t[ap] == IGNORE);
				sub(cnf, to_string(ap+1), 0, h);
				t[ap] = 0;
			}
			else
			{
				int ap = atoi(literal.c_str())-1;
				assert(t[ap] == IGNORE);
				sub(cnf, to_string(ap+1), 1, h);
				t[ap] = 1;
			}
		}
	}
}

// cnf - A formula represented in Conjunctive Normal Form
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(vector<list<string>> initial_cnf, const boost::timer::cpu_timer& timer, heuristic h)
{
	stack<update> truth_updates;
	stack<vector<list<string>>> cnf_set;
	stack<vector<int>> truth_set;
	cnf_set.push(move(initial_cnf));
	truth_set.push(vector<int>(vars, IGNORE));

	while(!cnf_set.empty() && (timer.elapsed().wall < timeout))
	{
		vector<list<string>> cnf = move(cnf_set.top());
		vector<int> t = move(truth_set.top());
		cnf_set.pop();
		truth_set.pop();

		if(!truth_updates.empty())
		{
			++split_count;
			update& u = truth_updates.top();
			sub(cnf, to_string(u.first+1), u.second, h);
			truth_updates.pop();
			//cout << split_count << " " << u.first << " " << u.second << endl;
		}

		// Unit Clause Propagation
		unit_propagation(cnf, t, h);

		// Check Formula
		switch(valid(cnf))
		{
			case UNSAT:
				{
					continue;
				}
			case SAT:
				{
					return t;
				}
		}	

		// Select AP without truth assignment
		update u;
		switch(h)
		{
			case Random:
				{
					// Random Heuristic
					u = random_heuristic(t);
				}
				break;
			case TwoClause:
				{
					// 2-Clause Heuristic
					u = two_clause_heuristic(t);
				}
				break;
			case MyHeuristic:
				{
					// TODO My Heuristic
					return vector<int>();
				}
				break;
			default:
				{
					u = basic_heuristic(t);
				}
		}
		//cout << "AP: " << to_string(u.first+1) << endl;
		assert(t[u.first] == IGNORE);

		vector<int> a1(t);
		a1[u.first] = u.second;
		truth_set.push(move(a1));
		truth_updates.push(move(u));
		cnf_set.push(cnf);

		t[u.first] = (1 - u.second);
		truth_set.push(move(t));
		truth_updates.push(make_pair(u.first, (1- u.second)));
		cnf_set.push(move(cnf));
	}
	return vector<int>();
}

vector<list<string>> parseCNF(const string& filename)
{
	vector<list<string>> cnf;
	list<string> clause;
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
					cnf.push_back(clause);
					clause.clear();
				}
				else
				{
					if(c.size() > 0)
						clause.push_back(c);
				}
				c.clear();
			}
		}
	}
	if(clause.size() > 0)
		cnf.push_back(clause);
	return cnf;
}

vector<list<string>> randomCNF(const int& N, const double& LProb, const double& LN_Ratio)
{
	std::uniform_int_distribution<int> p(1,N);
	std::uniform_real_distribution<double> l(0.0,1.0);

	int size = int(LN_Ratio * N);
	vector<list<string>> cnf(size);

	for(int n = 0; n < size; ++n)
	{
		for(int m = 0; m < K; ++m)
		{
			string literal;
			if(l(generator) > LProb)
			{
				literal.append(1, NEGATION);
			}
			literal.append(to_string(p(generator)));
			cnf[n].push_back(literal);
		}
	}
	return cnf;
}

void setup(int N, heuristic h)
{
	switch(h)
	{
		case TwoClause:
			{
				// Reset Two Clause Tracking List
				two_clauses.clear();
				two_clauses.resize(N, 0);
			}
			break;
	}
}

int main(int argc, char* argv[])
{
	srand (time(NULL));

	// Experiments - N, L-Probability, L/N Ratio
	if(argc == 4)
	{
		vars = atoi(argv[1]);
		double LProb = atof(argv[2]);
		double LN_Ratio = atof(argv[3]);
		cout << "N: " << vars << " L-Probability: " << LProb << " LN_Ratio: " << LN_Ratio << std::endl;         

		vector<int> success((int) Basic, 0);
		vector<vector<int>> split((int) Basic);
		vector<vector<double>> time((int) Basic);
		for(int h = 0; h < (int) Basic; ++h)
		{
			split[h].resize(ITER, 0);
			time[h].resize(ITER, 0);
		}

		boost::timer::cpu_timer timer;

		// Run benchmark for ITER iterations
		for(int n = 0; n < ITER; ++n)
		{
			const vector<list<string>> cnf = randomCNF(vars, LProb, LN_Ratio);
			for(int h = 0; h < HEURISTICS; ++h)
			{
				setup(vars, (heuristic) h);

				timer.start();
				vector<int> result = solve(cnf, timer, (heuristic) h);
				timer.stop();

				if(result.size() > 0)
				{
					++success[h];
				}

				split[h][n] = split_count;
				split_count = 0;

				time[h][n] = atof(timer.format(boost::timer::default_places, "%w").c_str());
				cout << hstr[h] << " - iteration: " << n << " time: " << time[h][n] << std::endl;
			}
		}

		for(int h = 0; h < HEURISTICS; ++h)
		{
			// Sort data and print median value
			cout << hstr[h] << " Success Rate: " << success[h] << endl;
			std::sort(split[h].begin(), split[h].end());
			std::sort(time[h].begin(), time[h].end());

			cout << "min number of splitting-rule applications: " << split[h][0] << endl;
			cout << "median number of splitting-rule applications: " << split[h][ITER/2] << endl;
			cout << "max number of splitting-rule applications: " << split[h][ITER-1] << endl;

			cout << "min computation time: " << time[h][0] << endl;
			cout << "median computation time: " << time[h][ITER/2] << endl;
			cout << "max computation time: " << time[h][ITER-1] << endl;
		}
	}

	// CNF Format File
	if(argc > 1)
	{
		heuristic h = Basic;
		if(argc == 3)
		{
			int value = atoi(argv[2]);
			if(value >= 0 && value < Basic)
				h = (heuristic) value;
		}

		const string file(argv[1]);
		const vector<list<string>> cnf = parseCNF(file);
		setup(vars, h);

		// Timer
		std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
		vector<int> result = solve(cnf, *timer, h);
		timer.reset(nullptr);

		print(result); 
		cout << hstr[h] << endl;
	}
}
