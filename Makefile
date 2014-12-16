CXXFLAGS = -O3 -std=c++11
CXX=g++
LD_FLAGS = -lboost_program_options -lboost_system -lboost_timer

all: sat cdcl

sat: sat.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< $(LD_FLAGS)

cdcl: cdcl.cpp
	$(CXX) $(CXXFLAGS) -o $@ $< $(LD_FLAGS)

einstein: einstein.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

key: key.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

pigeon: sat cdcl
	./sat pigeon-hole/hole6.cnf 1
	./sat pigeon-hole/hole7.cnf 1
	./sat pigeon-hole/hole8.cnf 1
	./sat pigeon-hole/hole9.cnf 1
	./sat pigeon-hole/hole10.cnf 1
	./cdcl pigeon-hole/hole6.cnf
	./cdcl pigeon-hole/hole7.cnf
	./cdcl pigeon-hole/hole8.cnf
	./cdcl pigeon-hole/hole9.cnf
	./cdcl pigeon-hole/hole10.cnf

benchmark: sat 
	./sat 100 0.5 3
	./sat 100 0.5 3.2
	./sat 100 0.5 3.4
	./sat 100 0.5 3.6
	./sat 100 0.5 3.8
	./sat 100 0.5 4
	./sat 100 0.5 4.2
	./sat 100 0.5 4.4
	./sat 100 0.5 4.6
	./sat 100 0.5 4.8
	./sat 100 0.5 5
	./sat 100 0.5 5.2
	./sat 100 0.5 5.4
	./sat 100 0.5 5.6
	./sat 100 0.5 5.8
	./sat 100 0.5 6

benchmark1: sat
	./sat 150 0.5 3
	./sat 150 0.5 3.2
	./sat 150 0.5 3.4
	./sat 150 0.5 3.6
	./sat 150 0.5 3.8
	./sat 150 0.5 4
	./sat 150 0.5 4.2
	./sat 150 0.5 4.4
	./sat 150 0.5 4.6
	./sat 150 0.5 4.8
	./sat 150 0.5 5
	./sat 150 0.5 5.2
	./sat 150 0.5 5.4
	./sat 150 0.5 5.6
	./sat 150 0.5 5.8
	./sat 150 0.5 6

test: sat tests/test.cnf tests/test1.cnf tests/test2.cnf tests/test3.cnf tests/test4.cnf tests/test5.cnf 
	./sat tests/test.cnf
	./sat tests/test1.cnf
	./sat tests/test2.cnf
	./sat tests/test3.cnf
	./sat tests/test4.cnf
	./sat tests/test5.cnf

othertest: cdcl tests/test.cnf tests/test1.cnf tests/test2.cnf tests/test3.cnf tests/test4.cnf tests/test5.cnf 
	./cdcl tests/test.cnf
	./cdcl tests/test1.cnf
	./cdcl tests/test2.cnf
	./cdcl tests/test3.cnf
	./cdcl tests/test4.cnf
	./cdcl tests/test5.cnf

clean:
	rm -rf sat
	rm -rf cdcl
	rm -rf einstein
	rm -rf key
