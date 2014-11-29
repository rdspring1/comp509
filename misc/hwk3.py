#!/usr/bin/env python
# Propositional Connectives:
# Not !
# Atomic Proposition = Integers
import copy

prepositional_connectives = ["!", "&", "^", "?", "="]
binary_connectives = ["&", "^", "?", "="]

# cnf - A formula represented in Conjunctive Normal Form
# prop - A set of truth assignments for AP
def sat_solver(cnf, prop):
   #print "sat: " + str(cnf)
   clause_sat = True

   # check if any clauses are empty: Not Satisfiable under current truth assignment
   # check if all clauses are True: Satisfiable
   for n in range(0, len(cnf)):
      if len(cnf[n]) == 0:
         return []
      elif len(cnf[n]) > 1 or isinstance(cnf[n][0], basestring):
         clause_sat = False

   if clause_sat:
      return prop

   # select AP without truth assignment
   ap = -1
   for n in range(0, len(prop)):
      if prop[n] < 0:
         ap = n
         break

   # check if satisfiable if AP = True
   prop[n] = True
   trueResult = sat_solver(sub(copy.deepcopy(cnf), ap, True), list(prop))
   #print "tR: " + str(trueResult)

   # check if satisfiable if AP = False
   prop[n] = False
   falseResult = sat_solver(sub(copy.deepcopy(cnf), ap, False), list(prop))
   #print "fR: " + str(falseResult)

   # return truth assignment if formula is satisfiable; otherwise return empty list
   if len(trueResult) < 1:
       return falseResult
   else:
       return trueResult

def sub(cnf, ap, value):
   #print "sub start: " + str(cnf)
   #print "ap: " + str(ap)
   #print "value: " + str(value)
   for i in range(0, len(cnf)):
      # empty_clause checks if the clause is empty
      empty_clause = True
      for j in range(0, len(cnf[i])):
         literal = cnf[i][j]

         if isinstance(literal, bool):
            empty_clause = not(literal)
         else:
            length = len(literal)
            if literal[length-1] == str(ap):
               # evaluate truth value for literal
               truth_value = value
               if length > 1:
                  truth_value = not(value)

               if truth_value:
                  cnf[i] = [True]
                  empty_clause = False
                  break
               else:
                  literal = cnf[i][j] = False

            if isinstance(literal, basestring):
               empty_clause = False

      if empty_clause:
         cnf[i] = []
   #print "sub end: " + str(cnf)
   return cnf
 
s1 = [ ["0", "2", "4"], ["0", "2", "!4", "1", "3"], ["0", "2", "!4", "!1", "!3"] ]
s2 = [ ["!0", "!3", "4", "1", "!2"], ["!0", "!3", "4", "!1", "2"] ]
s3 = [ ["!0", "!1", "2", "3"], ["!0", "!1", "!2", "!3"], ["!0", "!4", "2", "3"], ["!0", "!4", "!2", "!3"],
["1", "4", "3", "!4"], ["1", "4", "!3", "4"], ["0", "!2", "3"], ["0", "2", "!3"] ] 
s4 = s1 + s2 + s3
#print sat_solver(s1, [-1 for i in range(5)])
#print sat_solver(s2, [-1 for i in range(5)])
#print sat_solver(s3, [-1 for i in range(5)])
print sat_solver(s4, [-1 for i in range(5)])
     
# Unit Tests
#print sat_solver([["0"]], [-1 for i in range(1)]) # p
#print sat_solver([["!0"]], [-1 for i in range(1)]) # !p
#print sat_solver([["0"],["!0"]], [-1 for i in range(1)]) # p and !p
#print sat_solver([["1","0"]], [-1 for i in range(2)]) # p or q
#print sat_solver([["0"],["1"]], [-1 for i in range(2)]) # p and q
