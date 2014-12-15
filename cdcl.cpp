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

typedef std::pair<int, int> update;
typedef std::unordered_map<int, int> wlist;

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
const boost::timer::nanosecond_type TIMEOUT(60 * 1000000000LL);
std::default_random_engine generator( (unsigned int)time(NULL) );

enum state
{
    NONE,
    CONFLICT,
    SAT
};

// Implication Graph
vector<int> decision_level;
vector<int> parent;
vector<int> t;
list<int> updates;
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
    parent.clear();
    t.clear();
    decision_level.resize(vars, IGNORE);
    parent.resize(vars, IGNORE);
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

const int p[] = {41, 40, 39, 38, 37, 35, 34, 33, 32, 29, 28, 27, 23, 22, 17, 16, 5, 4, 10, 17, 10, 16, 21, 2, 17, 4, 22, 8, 17, 22, 15, 23, 20, 22, 10, 9, 15, 23, 15, 10, 2, 22, 8, 2, 21, 8, 17, 3, 3, 25, 2, 3, 27, 17, 9, 23, 22, 21, 17, 22, 8, 22, 21, 23, 17, 3, 16, 23, 3, 20, 23, 9, 22, 20, 20, 33, 20, 10, 32, 33, 1, 8, 3, 33, 23, 22, 21, 16, 16, 22, 32, 22, 21, 10, 14, 21, 10, 16, 9, 23, 33, 26, 33, 16, 9, 10, 32, 7, 27, 15, 9, 21, 19, 27, 9, 16, 9, 26, 13, 16, 9, 3, 19, 27, 3, 33, 9, 2, 7, 13, 27, 7, 20, 33, 3, 10, 28, 33, 3, 19, 33, 3, 8, 33, 3, 8, 30, 25, 2, 9, 28, 10, 16, 21, 28, 16, 28, 33, 10, 20, 9, 10, 16, 3, 10, 3, 8, 8, 21, 10, 22, 38, 39, 9, 1, 20, 9, 16, 16, 15, 10, 8, 39, 11, 16, 21, 10, 17, 22, 26, 38, 39, 27, 9, 26, 19, 7, 39, 3, 39, 27, 3, 19, 8, 39, 27, 3, 10, 28, 38, 2, 39, 3, 9, 37, 2, 7, 27, 38, 13, 39, 20, 21, 3, 39, 20, 24, 37, 38, 1, 7, 19, 13, 1, 8, 39, 21, 28, 16, 28, 22, 39, 22, 20, 16, 33, 15, 11, 15, 32, 10, 11, 10, 39, 13, 20, 32, 8, 19, 14, 32, 8, 2, 14, 13, 14, 20, 3, 33, 40, 2, 9, 11, 32, 3, 19, 32, 2, 33, 3, 3, 7, 32, 33, 20, 20, 7, 2, 38, 6, 1, 31, 33, 19, 3, 19, 13, 0, 31, 33, 19, 13, 19, 13, 18, 19, 13, 33, 3, 31, 7, 12, 18, 1, 19, 6, 32, 1, 19, 3, 13, 13, 39, 37, 20, 19, 31, 33, 1, 13, 1, 39, 28, 37, 39, 13, 3, 13, 1, 33, 39, 31, 26, 26, 13, 39, 19, 39, 19, 33, 2, 13, 39, 33, 19, 2, 39, 33, 39, 33, 2, 25, 12, 26, 31, 1, 39, 39, 37, 33, 1, 32, 20, 39, 33, 33, 37, 32, 39, 20, 31, 32, 25, 19, 39, 25, 20, 39, 20, 26, 0, 31, 19, 39, 39, 37, 25, 33, 31, 39, 7, 1, 37, 31, 0, 37, 32, 0, 32, 1, 7, 19, 25, 0, 7, 1, 19, 8, 25, 20, 2, 18, 39};
const int v[] = {0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1};
int prop = -1;

update myh_heuristic(const vector<int>& t)
{
    /*
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
    std::uniform_int_distribution<int> p(0,ties.size()-1);
    std::uniform_int_distribution<int> v(0,1);
    return make_pair(ties[p(generator)], v(generator));
    */
    return make_pair(p[++prop], v[prop]);
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

void update_watched_literal(bool first, int clause)
{
    //cout << "uwl: " << ((first) ? wl1[clause] : wl2[clause])  << endl;
    int other = (first) ? wl2[clause] : wl1[clause];
    int index = 0;
    for(const auto& literal : cnf[clause])
    {
        if(index != other && evaluate_literal(literal) != 0)
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
            return;
        }
        ++index;
    }
}

void evaluate_cnf()
{
    // Update Watchlist 1
    for(const auto& index : wl1)
    {
        int literal = cnf[index.first][index.second];
        int truth_value = evaluate_literal(literal);
        if(truth_value == 0)
        {
            update_watched_literal(true, index.first);
        }
    }

    // Update Watchlist 2
    for(const auto& index : wl2)
    {
        int literal = cnf[index.first][index.second];
        int truth_value = evaluate_literal(literal);
        if(truth_value == 0)
        {
            update_watched_literal(false, index.first);
        }
    }
}

void update_implication_graph(const int& ap, const int& value, const int& dl, const int& pc)
{
    cout << dl << " " << (ap+1) << " " << value << endl;
    assert(t[ap] == IGNORE);
    updates.push_front(ap+1);
    t[ap] = value;
    decision_level[ap] = dl;
    parent[ap] = pc;
}

state unit_propagation(int& clause_id, int dl)
{
    bool restart = false;
    do
    {
        restart = false;
        // check if any clauses are empty: Not Satisfiable under current truth assignment
        // check if all clauses are True: Satisfiable
        for(auto iter = cnf.begin(); iter != cnf.end(); ++iter)
        {
            int literal1 = iter->second[wl1[iter->first]];
            int literal2 = iter->second[wl2[iter->first]];
            int v1 = evaluate_literal(literal1);
            int v2 = evaluate_literal(literal2);

            if(v1 == 1 || v2 == 1)
            {
                // Clause is SAT
                continue;
            }
            else if(v1 == 0 && v2 == 0)
            {
                //cout << "CONFLICT: " << dl << endl;
                cout << "clause: " << iter->first << endl;
                //cout << "wl1: " << wl1[iter->first] << " wl2: " << wl2[iter->first] << endl;
                //cout << "l1: " << literal1 << " l2: " << literal2 << endl;
                //cout << "v1: " << v1 << " v2: " << v2 << endl;
                clause_id = iter->first;
                return CONFLICT;
            }
            else if(wl1[iter->first] != wl2[iter->first] && v1 == IGNORE && v2 == IGNORE)
            {
                continue;
            }
            else // Unit Clause
            {
                /*
                cout << "clause: " << iter->first << endl;
                cout << "size: " << iter->second.size() << endl;
                cout << "wl1: " << wl1[iter->first] << " wl2: " << wl2[iter->first] << endl;
                cout << "l1: " << literal1 << " l2: " << literal2 << endl;
                cout << "v1: " << v1 << " v2: " << v2 << endl;

                int count = 0;
                for(int l : iter->second)
                {
                    if(evaluate_literal(l) != 0)
                        ++count;
                }
                cout << "count: " << count << endl;
                assert(count == 1);
                */

                int literal = (v1 == IGNORE) ? literal1 : literal2;
                int value = (literal < 0) ? 0 : 1;
                int ap = abs(literal)-1;
                update_implication_graph(ap, value, dl, iter->first);
                evaluate_cnf();
                //cout << "update-clause: " << iter->first << " ap: " << (ap+1) << " value: " << value << endl;
                restart = true;
            }
        }
    } while (restart);
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
vector<int> analysis(const int& clause_id, int& dl, bool& change)
{
    // Collect all literals from parent clauses - Ignore Duplicates and conflicting variables
    // All literals in unsatisfied clause are false
    unordered_set<int> conflict_set(cnf[clause_id].begin(), cnf[clause_id].end());
    int literal = updates.front();

    while(!updates.empty() && !decision_count(conflict_set, dl))
    {
        //implied literals
        if(decision_level[literal-1] == dl && parent[literal-1] != IGNORE)
        {
            //cout << literal << " parent: " << parent[literal-1] << endl;
            change = true;

            // Resolution Implication Rule
            conflict_set.erase(literal);
            conflict_set.erase(-1 * literal);

            const vector<int>& clause = cnf[parent[literal-1]];
            for(const int& l : clause)
            {
                //cout << l << " ";
                if(abs(l) != literal && conflict_set.find(literal) == conflict_set.end())
                {
                    assert(evaluate_literal(l) == 0);
                    conflict_set.insert(l);
                }
            }
            //cout << endl;
        }

        //cout << "new: ";
        //for(int l : conflict_set)
        //{
        //    cout << l << " ";
        //    assert(evaluate_literal(l) == 0);
        //}
        //cout << endl;

        updates.pop_front();
        literal = updates.front();
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
    }

        for(int l : conflict_set)
        {
            cout << l << " ";
            assert(evaluate_literal(l) == 0);
        }
        cout << endl;

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
    while(!updates.empty() && decision_level[updates.front()-1] > dl)
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

                    // Conflict Analysis / New Decision Level
                    vector<int> conflict_clause = analysis(clause_id, dl, change);
                    if(dl < 0)
                    {
                        return vector<int>();
                    }
                    //cout << "conflict size: " << conflict_clause.size() << " new decision level: " << dl << endl;

                    // Update VSIDS Heuristic
                    update_heuristic(conflict_clause);
                    for(int i = 0; i < myh.size(); ++i)
                    {
                        myh[i] = round(myh[i]/DECAY);
                    }

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
                        evaluate_cnf();
                    }
                    ++backtrack_count;
                    //cout << backtrack_count << endl;
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
        //cout << "Decision: " << (u.first+1) << " " << u.second << endl;
        assert(t[u.first] == IGNORE);

        ++backtrack_count;
        update_implication_graph(u.first, u.second, ++dl, IGNORE);
        evaluate_cnf();
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
        timer.reset(nullptr);

        print(result); 
        cout << hstr[h] << " Timeout: " << timeout << endl;
        cout << "Number of backtracks: " << backtrack_count << endl;
        cout << "Number of added_clauses: " << added_clauses << endl;
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
