#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <stdlib.h>
#include <vector>
#include <stack>
#include <fstream>
#include <random>
#include <algorithm>
#include <memory>
#include <boost/timer/timer.hpp>

using namespace std;

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

int split_count = 0;
int vars = 0;

typedef std::pair<int, int> update;

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

vector<vector<string>> sub(const vector<vector<string>>& cnf, const string& ap, const int& value)
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

    vector<vector<string>> new_cnf;
    vector<string> new_clause;

    for(const auto& clause : cnf)
    {
        // empty_clause checks if the clause is empty
        bool empty_clause = true;
        for(const auto& literal : clause)
        {
            if(literal == TRUE)
            {
                new_clause.push_back(literal);
                empty_clause = false;
            }
            else if(literal != FALSE)
            {
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
                else
                {
                    new_clause.push_back(literal);
                    empty_clause = false;
                }

                if(match)
                {
                    if(truth_value)
                    {
                        new_clause = vector<string>(1, TRUE);
                        empty_clause = false;
                        break;
                    }
                    else
                    {
                        new_clause.push_back(FALSE);
                    }
                }
            }
        }

        // replace unsatisfiable disjunctive clauses with empty vector
        if(empty_clause)
        {
            new_cnf.push_back(vector<string>());
        }
        else
        {
            new_cnf.push_back(new_clause);
        }
        new_clause.clear();
    }

    /*
    cout << "sub end: " << new_cnf.size() << endl;
    int e = 0;
    for(auto& clause : new_cnf)
    {
        cout << "start clause: " << ++e << endl;
        for(auto& literal : clause)
        {
            cout << "literal: " <<  literal << endl;
        }
    }
    */
    assert(cnf.size() == new_cnf.size());
    return new_cnf;
}

int valid(const vector<vector<string>>& cnf)
{
    // check if any clauses are empty: Not Satisfiable under current truth assignment
    // check if all clauses are True: Satisfiable
    for(const auto& clause : cnf)
    {
        // Clause is False, Clause contains multiple propositions, singleton clause
        if(clause.size() == 0)
        {
            return UNSAT;
        }
        else if(clause.size() > 1 || clause[0] != TRUE)
        {
            return CONTINUE;
        }
    }
    return SAT;
}

// cnf - A formula represented in Conjunctive Normal Form
// prop - A set of truth assignments for AP
// return - a truth assignment if formula is satisfiable; otherwise return empty list
vector<int> solve(vector<vector<string>>& initial_cnf, vector<int>& initial_t)
{
    stack<vector<vector<string>>> cnf_set;
    stack<vector<int>> truth_set;
    cnf_set.push(move(initial_cnf));
    truth_set.push(move(initial_t));

    while(!cnf_set.empty())
    {
        ++split_count;
        vector<vector<string>> cnf = move(cnf_set.top());
        vector<int> t = move(truth_set.top());
        cnf_set.pop();
        truth_set.pop();

        for(const int& i : t)
        	cout << " " << i;
        cout << endl;

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
        // TODO Random Heuristic
        // TODO 2-Clause Heuristic
        // TODO My Heuristic
        int ap = IGNORE;
        for(int i = 0; i < t.size(); ++i)
        {
            if(t[i] < 0)
            {
                ap = i;
                break;
            }
        }
        assert(ap != IGNORE);
        //cout << "AP: " << to_string(ap+1) << endl;

        vector<int> true_assignment(t);
        true_assignment[ap] = 1;
        vector<vector<string>> true_cnf = sub(cnf, to_string(ap+1), 1);        
        truth_set.push(move(true_assignment));
        cnf_set.push(move(true_cnf));

        vector<int> false_assignment(t);
        false_assignment[ap] = 0;
        vector<vector<string>> false_cnf = sub(cnf, to_string(ap+1), 0);        
        truth_set.push(move(false_assignment));
        cnf_set.push(move(false_cnf));
    }

    return vector<int>();
}

vector<vector<string>> parseCNF(const string& filename)
{
    vector<vector<string>> cnf;
    vector<string> clause;
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

vector<vector<string>> randomCNF(const int& N, const double& LProb, const double& LN_Ratio)
{
    std::default_random_engine generator;
    std::uniform_int_distribution<int> p(1,N);
    std::uniform_real_distribution<double> l(0.0,1.0);

    int size = int(LN_Ratio * N);
    vector<vector<string>> cnf(size);

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
            vector<vector<string>> cnf = randomCNF(N, LProb, LN_Ratio);
            vector<int> t(N, IGNORE);

            timer.start();
            vector<int> result = solve(cnf, t);
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
        vector<vector<string>> cnf = parseCNF(file);
        vector<int> t(vars, IGNORE);

        // Timer
        std::unique_ptr<boost::timer::auto_cpu_timer> timer(new boost::timer::auto_cpu_timer());
        vector<int> result = solve(cnf, t);
        timer.reset(nullptr);

        cout << "RESULT" << endl;
        print(result); 
    }
}
