# Directories
OBJ_DIR = obj
BUILD_DIR = build

# Name
NAME = adler32

# Files
FST_FILE = code/Impl.Adler32.fst
KRML_OUTPUT = $(OBJ_DIR)/$(NAME).krml
C_OUTPUT = $(BUILD_DIR)/$(NAME).c
H_OUTPUT = $(BUILD_DIR)/$(NAME).h
EXE_OUTPUT = $(BUILD_DIR)/$(NAME)

# Default target
all: $(C_OUTPUT) $(H_OUTPUT)

# Generate the .krml file from F* code
$(KRML_OUTPUT): $(FST_FILE)
	fstar.exe --cache_dir $(OBJ_DIR) --codegen krml --krmloutput $(KRML_OUTPUT) $(FST_FILE)

# Generate C and H files from .krml
$(C_OUTPUT) $(H_OUTPUT): $(KRML_OUTPUT)
	krml -tmpdir $(BUILD_DIR) -no-prefix $(basename $(notdir $(FST_FILE))) $(KRML_OUTPUT) -o $(EXE_OUTPUT)

# Clean up generated files
clean:
	rm -rf $(OBJ_DIR) $(BUILD_DIR)

# Phony targets
.PHONY: all clean
