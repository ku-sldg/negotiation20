# Makefile for compiling and running server.hs

# Compiler and compiler flags
GHC = ghc
GHCFLAGS = -O2

# Target executable
TARGET = server

# Source files
SOURCES = server.hs

# Build rule
$(TARGET): $(SOURCES)
	$(GHC) $(GHCFLAGS) -o $@ $<

# Run rule
run: $(TARGET)
	./$(TARGET)

# Clean rule
clean:
	rm -f $(TARGET) *.o *.hi

.PHONY: run clean
