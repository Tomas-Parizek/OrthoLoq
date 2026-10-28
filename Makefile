CXX := clang++

TARGET := ortholoq
SOURCES := main.cpp Aig.cpp FormulaAnalysis.cpp FormulaSymmetry.cpp TheoremPatterns.cpp ExactTheory.cpp Parser.cpp Lattice.cpp GeneratedLattice.cpp LatticeCertificate.cpp Evaluator.cpp Solver.cpp Model.cpp
OBJECTS := $(SOURCES:.cpp=.o)

WARNINGS := -Wall -Wextra -Wpedantic -Wshadow -fno-omit-frame-pointer
CXXFLAGS ?= -std=c++20 -O2 -DNDEBUG $(WARNINGS)

.PHONY: all clean rebuild debug sanitize

all: $(TARGET)

$(TARGET): $(OBJECTS)
	$(CXX) $(CXXFLAGS) $(OBJECTS) -ldl -o $(TARGET)

%.o: %.cpp
	$(CXX) $(CXXFLAGS) -c $< -o $@

rebuild: clean all

debug:
	$(MAKE) clean
	$(MAKE) CXXFLAGS='-std=c++20 -O0 -g3 $(WARNINGS)'

sanitize:
	$(MAKE) clean
	$(MAKE) CXXFLAGS='-std=c++20 -O1 -g -fsanitize=address,undefined $(WARNINGS)'

clean:
	rm -f $(OBJECTS) $(TARGET)
