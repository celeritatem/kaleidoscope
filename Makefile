build:
	clang++ -g -O3 toy.cpp `llvm-config --cxxflags --ldflags --system-libs --libs core orcjit native` -o toy
