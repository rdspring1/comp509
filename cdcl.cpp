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

// Settings
const heuristic h = Random;
const int K = 3;
const double LProb = 0.5f;
const double min_LN = 3.0f;
const double max_LN = 6.0f;
const double inc_LN = 0.5f;
int vars = 100;
int split_count = 0;

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
const int ITER = 100;
const boost::timer::nanosecond_type timeout(60 * 1000000000LL);
std::default_random_engine generator( (unsigned int)time(NULL) );

enum state
{
    CONTINUE,
    UNSAT,
    SAT
};

// Implication Graph
vector<int> decision_level;
vector<int> parent;
vector<int> t;
vector<vector<int>> cnf;

// Two Watched Law - Lazy Data Structure
vector<int> wl1;
vector<int> wl2;

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

update myh_heuristic(const vector<int>& t)
{
    // TODO
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
    return make_pair(available[p(generator)], v(generator));
}

int evaluate_literal(const int& literal, const int& ap, const int& value)
{
    if(literal == ap)
    {
        return value;
    }
    else if(literal < 0)
    {
        if(abs(literal) == ap)
        {
            return (1 - value);
        }
    }
    return IGNORE;
}

int evaluate_literal(const int& literal)
{
    if(literal < 0)
    {
        return (1 - t[abs(literal)]);
    }
    return t[literal];
}

void update_watched_literal(bool first, int clause)
{
    int index = 0;
    for(const auto& literal : cnf[clause])
    {
        int truth_value = evaluate_literal(literal);
        if(truth_value == IGNORE)
        {
            if(first)
            {
                wl1[clause] = index;
            }
            else
            {
                wl2[clause] = index;
            }
        }
        ++index;
    }
}

void evaluate_cnf(const int& ap, const int& value)
{
    int i = 0;
    for(const auto& clause : cnf)
    {
        int j = 0;
        for(const auto& literal : clause)
        {
            // evaluate truth value for literal
            int truth_value = evaluate_literal(literal, ap, value);

            if(truth_value != IGNORE)
            {
                if(truth_value)
                {
                    wl1[i] = j;    
                }
                else if(wl1[i] == j)
                {   
                    update_watched_literal(true, i);
                }
                else if(wl2[i] == j)
                {
                    update_watched_literal(false, i);
                }
            }
            ++j;
        }
        ++i;
    }
}

void unit_propagation()
{
    for(int i = 0; i < cnf.size(); ++i)
    {
        if(wl1[i] == wl2[i] && wl1[i] == IGNORE)
        {
            int literal = cnf[i][wl1[i]];
            if(literal < 0)
            {
                int ap = abs(literal);
                assert(t[ap] == IGNORE);
                t[ap] = 1;
                evaluate_cnf(ap, 0);
            }
            else
            {
                assert(t[literal] == IGNORE);
                t[literal] = 1;
                evaluate_cnf(literal, 1);
            }
            i = 0;
        }
    }
}

state valid()
{
    // check if any clauses are empty: Not Satisfiable under current truth assignment
    // check if all clauses are True: Satisfiable
    state clause_sat = SAT;
    for(int i = 0; i < cnf.size(); ++i)
    {
        int v1 = evaluate_literal(wl1[i]);
        int v2 = evaluate_literal(wl2[i]);
        // Clause is False, Clause contains multiple propositions, singleton clause
        if(v1 == 0 && v2 == 0)
        {
            return UNSAT;
        }
        else if(v1 == IGNORE || v2 == IGNORE)
        {
            clause_sat = CONTINUE;
        }
    }
    return clause_sat;
}

void update_implication_graph(const int& ap, const int& value, const int& dl, const int& pc)
{
    assert(t[ap] == IGNORE);
    t[ap] = value;
    decision_level[ap] = dl;
    parent[ap] = pc;
}

// cnf - A formula represented in Conjunctive Normal Form
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(const boost::timer::cpu_timer& timer, heuristic h)
{
    stack<update> truth_updates;
    do
    {
        // Unit Clause Propagation
        unit_propagation();

        // Check Formula
        switch(valid())
        {
            case UNSAT:
                {
                    if(!truth_updates.empty())
                    {
                        // TODO Conflict Analysis / Decision Level
                        // TODO Update Truth Assignment, VSIDS, Decision Level / Add Conflict Clause

                        ++split_count;
                        update& u = truth_updates.top();
                        truth_updates.pop();
                        //cout << split_count << " " << u.first << " " << u.second << endl;
                    }
                }
                continue;
            case SAT:
                {
                    return t;
                }
        }	

        // Branching Heuristic - Select AP without truth assignment
        update u;
        switch(h)
        {
            case Random:
                {
                    // Random Heuristic
                    u = random_heuristic(t);
                }
                break;
            case MyHeuristic:
                {
                    // My Heuristic - Dynamic Largest Individual Sum
                    u = myh_heuristic(t);
                }
                break;
        }
        //cout << "AP: " << to_string(u.first+1) << endl;
        assert(t[u.first] == IGNORE);

        ++split_count;
        truth_updates.push(make_pair(u.first, (1-u.second)));
        update_implication_graph(u.first, u.second, truth_updates.size(), IGNORE);
        evaluate_cnf(u.first, u.second);
    } while(!truth_updates.empty() && (timer.elapsed().wall < timeout));

    return vector<int>();
}

vector<vector<int>> parseCNF(const string& filename)
{
    vector<vector<int>> cnf;
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
                    cnf.push_back(clause);
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
        cnf.push_back(clause);
    return cnf;
}

vector<vector<int>> randomCNF(const int& N, const double& LProb, const double& LN_Ratio)
{
    std::uniform_int_distribution<int> p(1,N);
    std::uniform_real_distribution<double> l(0.0,1.0);

    int size = int(LN_Ratio * N);
    vector<vector<int>> cnf(size);

    for(int n = 0; n < size; ++n)
    {
        for(int m = 0; m < K; ++m)
        {
            int literal = p(generator);
            if(l(generator) > LProb)
            {
                literal *= -1;
            }
            cnf[n].push_back(literal);
        }
    }
    return cnf;
}

void setup(heuristic h)
{
    decision_level.clear();
    parent.clear();
    t.clear();
    wl1.clear();
    wl2.clear();

    decision_level.resize(vars, IGNORE);
    parent.resize(vars, IGNORE);
    t.resize(vars, IGNORE);
    wl1.resize(cnf.size(), 0);
    wl2.resize(cnf.size(), K-1);

    switch(h)
    {
        case MyHeuristic:
            {
            }
            break;
    }
}

int main(int argc, char* argv[])
{
    // CNF Format File
    if(argc > 1)
    {
        const string file(argv[1]);
        cnf = parseCNF(file);
        setup(h);

        // Timer
        std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
        vector<int> result = solve(*timer, h);
        timer.reset(nullptr);

        print(result); 
        cout << hstr[h] << endl;
        return 0;
    }

    for(double LN_Ratio = min_LN; LN_Ratio <= max_LN; LN_Ratio += inc_LN)
    {
        int success = 0;
        vector<int> split(ITER, 0);
        vector<double> time(ITER, 0);

        boost::timer::cpu_timer timer;

        // Run benchmark for ITER iterations
        for(int n = 0; n < ITER; ++n)
        {
            cnf = randomCNF(vars, LProb, LN_Ratio);
            setup((heuristic) h);

            timer.start();
            vector<int> result = solve(timer, (heuristic) h);
            timer.stop();

            if(result.size() > 0)
            {
                ++success;
            }

            split[n] = split_count;
            split_count = 0;

            time[n] = atof(timer.format(boost::timer::default_places, "%w").c_str());
            cout << hstr[h] << " - iteration: " << n << " time: " << time[n] << std::endl;
        }

        // Sort data and print median value
        cout << "N: " << vars << " L-Probability: " << LProb << " LN_Ratio: " << LN_Ratio << std::endl;         
        cout << hstr[h] << " Success Rate: " << success << endl;
        std::sort(split.begin(), split.end());
        std::sort(time.begin(), time.end());

        cout << "min number of splitting-rule applications: " << split[0] << endl;
        cout << "median number of splitting-rule applications: " << split[ITER/2] << endl;
        cout << "max number of splitting-rule applications: " << split[ITER-1] << endl;

        cout << "min computation time: " << time[0] << endl;
        cout << "median computation time: " << time[ITER/2] << endl;
        cout << "max computation time: " << time[ITER-1] << "\n" << endl;
    }
}