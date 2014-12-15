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

const int TRUE = 0;
const int IGNORE = -1;
const int K = 3;
const int ITER = 100;
const boost::timer::nanosecond_type TIMEOUT(60 * 1000000000LL);
std::default_random_engine generator( (unsigned int)time(NULL) );

// Heuristic
enum heuristic
{
    MyHeuristic,
    TwoClause,
    Random,
    Basic 
};
const string hstr[] = 
{
    "MyHeuristic", 
    "TwoClause", 
    "Random", 
    "Basic"
};
const float psize[]
{
    0.0f,
    0.5f,
    0.25f,
    0.125
};
const int HEURISTICS = (int) Random;

enum state
{
    CONTINUE,
    UNSAT,
    SAT
};

// MyHeuristic
vector<float> myh;
vector<float> nc;

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

void update_heuristic(heuristic h, const int& ap, int size, bool neg)
{
    switch(h)
    {
        case MyHeuristic:
            {
                int value = ap-1;
                if(neg)
                {
                    nc[value] += psize[size];
                }
                myh[value] += psize[size];
                assert(value < myh.size());
                assert(value >= 0);
            }
            break;
    }
}

void sub_heuristic(heuristic h, const list<int>& clause)
{
    switch(h)
    {
        case TwoClause:
            {
                if(clause.size() == 2)
                {
                    for(const auto& literal : clause)
                    {
                        int value = abs(literal)-1;
                        ++two_clauses[value];
                        assert(value < two_clauses.size());
                        assert(value >= 0);
                    }
                }
            }
            break;
            /*
               case MyHeuristic:
               {
               for(const auto& literal : clause)
               {
               if(literal != TRUE)
               {
               int value = abs(literal)-1;
               if(literal < 0)
               {
               nc[value] += psize[clause.size()];
               }
            //myh[value] += std::pow(2, -1.0f * clause.size());
            myh[value] += psize[clause.size()];
            assert(value < myh.size());
            assert(value >= 0);
            }
            }
            }
            break;
             */
    }
}

void sub(vector<list<int>>& cnf, const int& ap, const int& value, heuristic h)
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
            else if(literal < 0)
            {
                int prop = abs(literal);
                if(prop == ap)
                {
                    truth_value = !truth_value;
                    match = true;
                }
                else
                {
                    update_heuristic(h, prop, clause.size(), true);
                }
            }
            else if(literal != TRUE)
            {
                update_heuristic(h, literal, clause.size(), false);
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

        sub_heuristic(h, clause);
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

state valid(const vector<list<int>>& cnf)
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

update myh_heuristic(const vector<int>& t)
{
    vector<int> ties;
    float maxValue = 0;
    for(int i = 0; i < myh.size(); ++i)
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
        myh[i] = 0;
        nc[i] = 0;
    }
    std::uniform_int_distribution<int> p(0,ties.size()-1);
    int index = ties[p(generator)];
    int pc = myh[index] - nc[index];
    if(pc > nc[index])
    {
        return make_pair(index, 0);
    }
    return make_pair(index, 1);
}

update two_clause_heuristic(const vector<int>& t)
{
    vector<int> ties;
    int maxValue = 0;
    for(int i = 0; i < t.size(); ++i)
    {
        if(t[i] == IGNORE)
        {
            if(two_clauses[i] > maxValue)
            {
                maxValue = two_clauses[i];
                ties.clear();
            }

            if(two_clauses[i] == maxValue)
            {
                ties.push_back(i);
            }
        }
        two_clauses[i] = 0;
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

void unit_propagation(vector<list<int>>& cnf, vector<int>& t, heuristic h)
{
    for(int i = 0; i < cnf.size(); ++i)
    {
        const list<int>& clause = cnf[i];
        if(clause.size() == 1 && clause.front() != TRUE)
        {
            int literal = clause.front();
            if(literal < 0)
            {
                int ap = abs(literal)-1;
                assert(t[ap] == IGNORE);
                sub(cnf, ap+1, 0, h);
                t[ap] = 0;
            }
            else
            {
                assert(t[literal-1] == IGNORE);
                sub(cnf, literal, 1, h);
                t[literal-1] = 1;
            }
            i = -1;
        }
    }
}

// cnf - A formula represented in Conjunctive Normal Form
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(vector<list<int>> initial_cnf, const boost::timer::cpu_timer& timer, heuristic h)
{
    stack<update> truth_updates;
    stack<vector<list<int>>> cnf_set;
    stack<vector<int>> truth_set;

    vector<list<int>> cnf = move(initial_cnf);
    vector<int> t(vars, IGNORE);
    while(timer.elapsed().wall < TIMEOUT)
    {
        // Unit Clause Propagation
        unit_propagation(cnf, t, h);

        // Check Formula
        switch(valid(cnf))
        {
            case UNSAT:
                {
                    if(!truth_updates.empty())
                    {
                        cnf = move(cnf_set.top());
                        t = move(truth_set.top());
                        cnf_set.pop();
                        truth_set.pop();

                        ++split_count;
                        update& u = truth_updates.top();
                        sub(cnf, u.first+1, u.second, h);
                        truth_updates.pop();
                    }
                    else
                    {
                        return vector<int>();
                    }
                    //cout << truth_updates.size() << " " << split_count << " " << u.first << " " << u.second << endl;
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
            case TwoClause:
                {
                    // 2-Clause Heuristic
                    u = two_clause_heuristic(t);
                }
                break;
            case MyHeuristic:
                {
                    // My Heuristic - Dynamic Largest Individual Sum
                    u = myh_heuristic(t);
                }
                break;
            default:
                {
                    u = basic_heuristic(t);
                }
        }
        //cout << "AP: " << to_string(u.first+1) << endl;
        assert(t[u.first] == IGNORE);

        vector<int> branch_truth_set(t);
        branch_truth_set[u.first] = (1 - u.second);
        truth_set.push(move(branch_truth_set));
        truth_updates.push(make_pair(u.first, (1-u.second)));
        cnf_set.push(cnf);

        ++split_count;
        t[u.first] = u.second;
        sub(cnf, u.first+1, u.second, h);
    }
    return vector<int>();
}

vector<list<int>> parseCNF(const string& filename)
{
    vector<list<int>> cnf;
    list<int> clause;
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

vector<list<int>> randomCNF(const int& N, const double& LProb, const double& LN_Ratio)
{
    std::uniform_int_distribution<int> p(1,N);
    std::uniform_real_distribution<double> l(0.0,1.0);

    int size = int(LN_Ratio * N);
    vector<list<int>> cnf(size);

    for(int n = 0; n < size; ++n)
    {
        for(int m = 0; m < K; ++m)
        {
            int literal = p(generator);
            if(l(generator) > LProb)
            {
                literal *= -1;;
            }
            cnf[n].push_back(literal);
        }
    }
    return cnf;
}

void setup(const vector<list<int>>& cnf, heuristic h)
{
    switch(h)
    {
        case TwoClause:
            {
                // Reset Two Clause Tracking List
                two_clauses.clear();
                two_clauses.resize(vars, 0);
            }
            break;
        case MyHeuristic:
            {
                myh.clear();
                nc.clear();
                myh.resize(vars, 0);
                nc.resize(vars, 0);
                for(const auto& clause : cnf)
                {
                    for(const auto& literal : clause)
                    {
                        if(literal < 0)
                        {
                            update_heuristic(h, abs(literal), clause.size(), true);
                        }
                        else
                        {
                            update_heuristic(h, literal, clause.size(), false);
                        }
                    }
                }
            }
            break;
    }
}

int main(int argc, char* argv[])
{
    // Experiments - N, L-Probability, L/N Ratio
    if(argc == 4)
    {
        vars = atoi(argv[1]);
        double LProb = atof(argv[2]);
        double LN_Ratio = atof(argv[3]);
        cout << "N: " << vars << " L-Probability: " << LProb << " LN_Ratio: " << LN_Ratio << std::endl;         

        vector<int> success((int) Basic, 0);
        vector<int> timeouts((int) Basic, 0);
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
            const vector<list<int>> cnf = randomCNF(vars, LProb, LN_Ratio);
            for(int h = 0; h < HEURISTICS; ++h)
            {
                setup(cnf, (heuristic) h);
                bool timeout = false;
                timer.start();
                vector<int> result = solve(cnf, timer, (heuristic) h);
                timer.stop();

                if(timer.elapsed().wall >= TIMEOUT)
                {
                    timeout = true;
                    ++timeouts[h];
                }

                if(result.size() > 0)
                {
                    ++success[h];
                }

                split[h][n] = split_count;
                split_count = 0;

                time[h][n] = atof(timer.format(boost::timer::default_places, "%w").c_str());
                //cout << hstr[h] << " - iteration: " << n << " time: " << time[h][n] << " timeout: " << timeout << std::endl;
            }
        }

        for(int h = 0; h < HEURISTICS; ++h)
        {
            // Sort data and print median value
            cout << hstr[h] << " Success Rate: " << success[h] << " Timeouts: " << timeouts[h] << endl;
            std::sort(split[h].begin(), split[h].end());
            std::sort(time[h].begin(), time[h].end());

            cout << "min number of splitting-rule applications: " << split[h][0] << endl;
            cout << "median number of splitting-rule applications: " << split[h][ITER/2] << endl;
            cout << "max number of splitting-rule applications: " << split[h][ITER-1] << endl;

            cout << "min computation time: " << time[h][0] << endl;
            cout << "median computation time: " << time[h][ITER/2] << endl;
            cout << "max computation time: " << time[h][ITER-1] << "\n" << endl;
        }
        return 0;
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
        const vector<list<int>> cnf = parseCNF(file);
        setup(cnf, h);

        bool timeout = false;
        // Timer
        std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
        vector<int> result = solve(cnf, *timer, h);
        if(timer->elapsed().wall >= TIMEOUT)
        {
            timeout = true;
        }
        timer.reset(nullptr);

        print(result); 
        cout << "Timeout: " << timeout << endl;
        cout << hstr[h] << endl;
    }
}
