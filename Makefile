CXXFLAGS = -g -std=c++11
CXX=g++
LD_FLAGS = -lboost_program_options -lboost_system -lboost_timer

all: sat

sat: sat.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< $(LD_FLAGS)

einstein: einstein.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

key: key.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

benchmark: sat 
	./sat 100 0.5 3
	./sat 100 0.5 3.5
	./sat 100 0.5 4
	./sat 100 0.5 4.5
	./sat 100 0.5 5
	./sat 100 0.5 5.5
	./sat 100 0.5 6

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
	rm -rf key
