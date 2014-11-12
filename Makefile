CXXFLAGS = -g -std=c++11
CXX=g++

all: sat einstein

sat: sat.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

einstein: einstein.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

test: sat tests/test.cnf tests/test1.cnf tests/test2.cnf tests/test3.cnf tests/test4.cnf tests/test5.cnf 
	./sat tests/test.cnf
	./sat tests/test1.cnf
	./sat tests/test2.cnf
	./sat tests/test3.cnf
	./sat tests/test4.cnf
	./sat tests/test5.cnf

clean:
	rm -rf sat
	rm -rf einstein
