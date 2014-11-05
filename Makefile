CXXFLAGS = -g -std=c++11
CXX=g++

sat: sat.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -rf sat
