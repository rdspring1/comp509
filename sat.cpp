#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <fstream>

using namespace std;

const string UNSAT = "UNSAT";
const string VAR = "VARIABLE";
const string TRUTH = "Truth Assignment";
const string COMMENT = "c";
const string PROBLEM = "p";
const string END = "0";
const string cnf_format = "cnf";
const string sat_format = "sat";
int vars = 0;
int ignore = -1;

void print(vector<int> t)
{
    if(t.size() == 0)
    {
        cout << UNSAT << endl;
    }

    for(int i = 0; i < t.size(); ++i)
    {
        if(t[i] != ignore)
            cout << VAR << " " << (i+1) << " " << TRUTH << " " <<  bool(t[i]) << endl;
        else
            cout << VAR << " " << (i+1) << " " << TRUTH << " " <<  t[i] << endl;
    }
}

vector<int> solve(vector<vector<string>> cnf, vector<int> t)
{
    return t;
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
                    clause.push_back(c);
                }
                c.clear();
            }
        }
    }
    cnf.push_back(clause);
    return cnf;
}

int main(int argc, char* argv[])
{
    const string file(argv[1]);
    vector<vector<string>> cnf = parseCNF(file);
    vector<int> t(vars, ignore);
    vector<int> result = solve(cnf, t);
    print(result); 
}
