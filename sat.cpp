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

const int UNSAT = -1;
const int CONTINUE = 0;
const int SAT = 1;
const int IGNORE = -1;
const int K = 3;
const int ITER = 100;
const boost::timer::nanosecond_type timeout(10 * 1000000000LL);
std::default_random_engine generator;

// Heuristic
enum heuristic
{
    Random,
    TwoClause,
    MyHeuristic,
    Basic 
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

void sub(vector<list<string>>& cnf, const string& ap, const int& value)
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

        if(clause.size() == 2)
        {
            for(auto& literal : clause)
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

int valid(const vector<list<string>>& cnf)
{
    // check if any clauses are empty: Not Satisfiable under current truth assignment
    // check if all clauses are True: Satisfiable
    int clause_sat = SAT;
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

update two_clause_heuristic()
{
    auto max_it = max_element(two_clauses.begin(), two_clauses.end());
    *max_it = 0;
    return make_pair(*max_it, 0);
}

update random_heuristic(const vector<int>& t)
{
    vector<int> available;
    for(int i = 0; i < t.size(); ++i)
    {
        if(t[i] < 0)
        {
            available.push_back(i);
        }
    }
    std::uniform_int_distribution<int> p(0,available.size());
    return make_pair(p(generator), 0);
}

update basic_heuristic(const vector<int>& t)
{
    for(int i = 0; i < t.size(); ++i)
    {
        if(t[i] < 0)
        {
            return make_pair(i, 0);
        }
    }
    assert(true);
}

// cnf - A formula represented in Conjunctive Normal Form
// prop - A set of truth assignments for AP
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(vector<list<string>>& initial_cnf, vector<int>& initial_t, const boost::timer::cpu_timer& timer, heuristic h = TwoClause)
{
    stack<update> truth_updates;
    stack<vector<list<string>>> cnf_set;
    stack<vector<int>> truth_set;
    cnf_set.push(move(initial_cnf));
    truth_set.push(move(initial_t));

    while(!cnf_set.empty() && (timer.elapsed().wall < timeout))
    {
        vector<list<string>> cnf = move(cnf_set.top());
        vector<int> t = move(truth_set.top());
        cnf_set.pop();
        truth_set.pop();

        //for(const int& i : t)
        //	cout << " " << i;
        //cout << endl;

        if(!truth_updates.empty())
        {
            ++split_count;
            update& u = truth_updates.top();
            //cout << split_count << " " << u.first << " " << u.second << endl;
            sub(cnf, to_string(u.first+1), u.second);
            truth_updates.pop();
        }

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
                    // TODO 2-Clause Heuristic
                }
                break;
            case MyHeuristic:
                {
                    // TODO My Heuristic
                }
                break;
            default:
                {
                    u = basic_heuristic(t);
                }
        }
        //cout << "AP: " << to_string(u.first+1) << endl;

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

int main(int argc, char* argv[])
{
    // Experiments - N, L-Probability, L/N Ratio
    if(argc == 4)
    {
        int N = atoi(argv[1]);
        double LProb = atof(argv[2]);
        double LN_Ratio = atof(argv[3]);
        cout << "N: " << N << " L-Probability: " << LProb << " LN_Ratio: " << LN_Ratio << std::endl;         

        int success = 0;
        vector<int> split(ITER, 0);
        vector<double> time(ITER, 0);
        boost::timer::cpu_timer timer;

        // Run benchmark for ITER iterations
        for(int n = 0; n < ITER; ++n)
        {
            // Reset Two Clause Tracking List
            two_clauses.clear();
            two_clauses.resize(N, 0);

            vector<list<string>> cnf = randomCNF(N, LProb, LN_Ratio);
            vector<int> t(N, IGNORE);

            timer.start();
            vector<int> result = solve(cnf, t, timer);
            timer.stop();

            if(result.size() > 0)
            {
                ++success;
            }

            split[n] = split_count;
            split_count = 0;

            time[n] = atof(timer.format(boost::timer::default_places, "%w").c_str());
            cout << "iteration: " << n << " time: " << time[n] << std::endl;
        }

        // Sort data and print median value
        cout << "Success Rate: " << success << endl;
        std::sort(split.begin(), split.end());
        std::sort(time.begin(), time.end());
        cout << "Total Number of Splitting-Rule Applications: " << split[ITER/2] << endl;
        cout << "Total Computation Time: " << time[ITER/2] << endl;
    }

    // CNF Format File
    if(argc == 2)
    {
        const string file(argv[1]);
        vector<list<string>> cnf = parseCNF(file);
        vector<int> t(vars, IGNORE);
        // Reset Two Clause Tracking List
        two_clauses.resize(vars, 0);

        // Timer
        std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
        vector<int> result = solve(cnf, t, *timer);
        timer.reset(nullptr);

        cout << "RESULT" << endl;
        print(result); 
    }
}
