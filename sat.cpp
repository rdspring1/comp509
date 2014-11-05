#include <assert.h>
#include <iostream>
#include <string>
#include <sstream>
#include <vector>
#include <fstream>

using namespace std;

const string TRUE = "True";
const string FALSE = "False";
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

vector<vector<string>> sub(vector<vector<string>> cnf, const string& ap, int value)
{
	/*
	cout << "sub start" << endl;
	for(auto& clause : cnf)
	{
		for(auto& literal : clause)
		{
			cout << "literal: " <<  literal << endl;
		}
		cout << "end clause" << endl;
	}
	cout << "ap: " << ap << endl;
	cout << "value: " << value << endl;
	*/

	for(auto& clause : cnf)
	{
		// empty_clause checks if the clause is empty
		bool empty_clause = true;
		for(auto& literal : clause)
		{
			if(literal == TRUE)
			{
				empty_clause = false;
			}
			else if(literal == FALSE)
			{
				empty_clause = true;
			}
			else
			{
				if(literal[literal.size()-1] ==  ap[0])
				{
					// evaluate truth value for literal
					bool truth_value = bool(value);
					if(literal.size() > 1)
					{
						truth_value = !truth_value;
					}

					if(truth_value)
					{
						clause = vector<string>(1, TRUE);
						empty_clause = false;
						break;
					}
					else
					{
						literal = FALSE;
					}
				}
				else
				{
					empty_clause = false;
				}
			}
		}
		if(empty_clause)
		{
			clause.clear();
		}
	}

	/*
	cout << "sub end" << endl;
	for(auto& clause : cnf)
	{
		for(auto& literal : clause)
		{
			cout << "literal: " <<  literal << endl;
		}
		cout << "end clause" << endl;
	}
	*/
	return cnf;
}

// cnf - A formula represented in Conjunctive Normal Form
// prop - A set of truth assignments for AP
vector<int> solve(vector<vector<string>> cnf, vector<int> t)
{
	bool clause_sat = true;
	// check if any clauses are empty: Not Satisfiable under current truth assignment
	// check if all clauses are True: Satisfiable
	for(const auto& clause : cnf)
	{
		if(clause.size() == 0)
		{
			return vector<int>();
		}
		else if(clause.size() > 1 || clause[0] != TRUE)
		{
			clause_sat = false;
		}
	}

	if(clause_sat)
		return t;

	// select AP without truth assignment
	int ap = ignore;
	for(int i = 0; i < t.size(); ++i)
	{
		if(t[i] < 0)
		{
			ap = i;
			break;
		}
	}
	assert(ap != ignore);

	// check if satisfiable if AP = True
	t[ap] = 1;
	vector<int> trueResult = solve(sub(cnf, to_string(ap+1), 1), t);
	//cout << "tR: " << trueResult << endl;

	// check if satisfiable if AP = False
	t[ap] = 0;
	vector<int> falseResult = solve(sub(cnf, to_string(ap+1), 0), t);
	//cout << "fR: " << falseResult << endl;

	// return truth assignment if formula is satisfiable; otherwise return empty list
	if(trueResult.size() < 1)
	{
		return falseResult;
	}
	else
	{
		return trueResult;
	}
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
