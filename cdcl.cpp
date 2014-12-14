#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <vector>
#include <list>
#include <unordered_set>
#include <fstream>
#include <random>
#include <algorithm>
#include <memory>
#include <math.h>
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
const heuristic h = MyHeuristic;
const int K = 3;
const double LProb = 0.5f;
const double min_LN = 3.0f;
const double max_LN = 6.0f;
const double inc_LN = 0.5f;
const float DECAY = 2.0f;
const float RESTART_INIT = 20;
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
const boost::timer::nanosecond_type TIMEOUT(10 * 1000000000LL);
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
vector<vector<int>> cnf;

// Two Watched Law - Lazy Data Structure
vector<int> wl1;
vector<int> wl2;

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

    if(!restart)
    {
        conflict_count = 0;
        wl1.clear();
        wl2.clear();
        wl1.resize(cnf.size(), 0);
        wl2.resize(cnf.size(), 0);
        for(int i = 0; i < cnf.size(); ++i)
        {
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
                    update_heuristic(clause);
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
    std::uniform_int_distribution<int> p(0,ties.size()-1);
    std::uniform_int_distribution<int> v(0,1);
    return make_pair(ties[p(generator)], v(generator));
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
    int prop = abs(literal)-1;
    if(prop == ap)
    {
        if(literal < 0)
        {
            return (1 - value);
        }
        return value;
    }
    return IGNORE;
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

void evaluate_cnf(const int& ap, const int& value)
{
    // Update Watchlist 1
    for(int i = 0; i < wl1.size(); ++i)
    {
        int literal1 = cnf[i][wl1[i]];
        int truth_value = evaluate_literal(literal1, ap, value);
        if(truth_value == 0)
        {
            update_watched_literal(true, i);
        }
    }

    // Update Watchlist 2
    for(int i = 0; i < wl1.size(); ++i)
    {
        int literal1 = cnf[i][wl2[i]];
        int truth_value = evaluate_literal(literal1, ap, value);
        if(truth_value == 0)
        {
            update_watched_literal(false, i);
        }
    }
}

void update_implication_graph(const int& ap, const int& value, const int& dl, const int& pc)
{
    assert(t[ap] == IGNORE);
    t[ap] = value;
    decision_level[ap] = dl;
    parent[ap] = pc;
}

state unit_propagation(int& clause_id, int dl)
{
    // check if any clauses are empty: Not Satisfiable under current truth assignment
    // check if all clauses are True: Satisfiable
    for(int i = 0; i < cnf.size(); ++i)
    {
        int literal1 = cnf[i][wl1[i]];
        int literal2 = cnf[i][wl2[i]];
        int v1 = evaluate_literal(literal1);
        int v2 = evaluate_literal(literal2);

        if(v1 == 1 || v2 == 1)
        {
            // Clause is SAT
            continue;
        }
        else if(v1 == 0 && v2 == 0)
        {
            clause_id = i;
            //cout << "CONFLICT: " << dl << endl;
            //cout << "clause: " << i << endl;
            //cout << "wl1: " << wl1[i] << " wl2: " << wl2[i] << endl;
            //cout << "l1: " << literal1 << " l2: " << literal2 << endl;
            //cout << "v1: " << v1 << " v2: " << v2 << endl;
            return CONFLICT;
        }
        else if(wl1[i] != wl2[i] && v1 == IGNORE && v2 == IGNORE)
        {
            continue;
        }
        else // Unit Clause
        {
            //cout << "clause: " << i << endl;
            //cout << "wl1: " << wl1[i] << " wl2: " << wl2[i] << endl;
            //cout << "l1: " << literal1 << " l2: " << literal2 << endl;
            //cout << "v1: " << v1 << " v2: " << v2 << endl;
            int literal = -1;
            if(v1 == IGNORE)
            {
                literal = literal1;
            }
            else
            {
                literal = literal2;
            }

            if(literal < 0)
            {
                int ap = abs(literal)-1;
                assert(t[ap] == IGNORE);
                //cout << "update1-clause: " << i << " ap: " << (ap+1) << " value: " << 0 << endl;
                update_implication_graph(ap, 0, dl, i);
                evaluate_cnf(ap, 0);
            }
            else
            {
                int ap = literal-1;
                assert(t[ap] == IGNORE);
                //cout << "update2-clause: " << i << " ap: " << (ap+1) << " value: " << 1 << endl;
                update_implication_graph(ap, 1, dl, i);
                evaluate_cnf(ap, 1);
            }
            i = -1;
        }
    }
    return NONE;
}

bool decision_count(const list<int>& clause, const int& dl)
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
    return (sigma == 1) || (xi == 0);
}

// Conflict Analysis / New Decision Level
vector<int> analysis(const int& clause_id, int& dl, bool& change)
{
    // Collect all literals from parent clauses - Ignore Duplicates and conflicting variables
    list<int> conflict_set(cnf[clause_id].begin(), cnf[clause_id].end()); 
    conflict_set.sort();
    conflict_set.unique();
    unordered_set<int> duplicates(conflict_set.begin(), conflict_set.end());
    int ap = abs(conflict_set.front())-1;

    while(!conflict_set.empty() && !decision_count(conflict_set, dl))
    {
        if(decision_level[ap] == dl && parent[ap] != IGNORE)
        {
            assert(t[ap] != IGNORE);
            change = true;

            // Resolution Implication Rule
            //cout << "a(l): " << parent[ap] << endl;
            int neg_literal = -1 * conflict_set.front();
            duplicates.erase(conflict_set.front());
            conflict_set.pop_front();

            const vector<int>& clause = cnf[parent[ap]];
            for(const int& literal : clause)
            {
                assert(t[abs(literal)-1] != IGNORE);
                //int others = count(conflict_set.begin(), conflict_set.end(), literal);
                if(literal != neg_literal && duplicates.find(literal) == duplicates.end())
                {
                    conflict_set.push_back(literal);
                    duplicates.insert(literal);
                }
            }
        }
        else
        {
            // Skip literal
            conflict_set.push_back(conflict_set.front());
            conflict_set.pop_front();
        }

        ap = abs(conflict_set.front())-1;
    }

    // Create Conflict Clause
    int max_dl = -1;
    int new_dl = -1;
    vector<int> conflict_clause;
    for(int literal : conflict_set)
    {
        int ap = abs(literal)-1;
        conflict_clause.push_back(literal);
        max_dl = max(max_dl, decision_level[ap]);
        if(decision_level[ap] != dl && decision_level[ap] > new_dl)
        {
            new_dl = decision_level[ap];
        }
    }

    if(max_dl <= 0)
    {
        dl = IGNORE;
    }
    else if(max_dl == dl)
    {
        // No Backtrack - Restart
        dl = 0;
    }
    else if(new_dl < dl)
    {
        // Normal Backtrack
        dl = new_dl;
    }
    //cout << "new dl: " << dl << endl;

    return conflict_clause;
}

// Update Truth Assignment
int update_truth_assignment(const int& dl)
{
    int decision = IGNORE;
    for(int ap = 0; ap < t.size(); ++ap)
    {
        if(decision_level[ap] >= dl)
        {
            if(parent[ap] == IGNORE && decision_level[ap] == dl)
            {
                decision = ap;
            }

            t[ap] = IGNORE;
            decision_level[ap] = IGNORE;
            parent[ap] = IGNORE;
        }
    }
    return decision;
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
                    if(change && conflict_clause.size() <= vars)
                    {
                        wl1.push_back(0);
                        wl2.push_back(conflict_clause.size()-1);
                        cnf.push_back(move(conflict_clause));
                        ++added_clauses;
                    }

                    // Update Truth Assignment
                    if(conflict_count > restart_threshold || dl == 0)
                    {
                        setup(h, true);
                    }
                    else
                    {
                        int ap = update_truth_assignment(dl);
                        update_implication_graph(ap, (1-t[ap]), dl++, IGNORE);
                        evaluate_cnf(ap, (1-t[ap]));
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
        evaluate_cnf(u.first, u.second);
    }

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
