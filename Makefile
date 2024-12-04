# Directoris
OBJ_DIR = obj
BUILD_DIR = build

NAME = adler32

# Files
FST_FILES = code/Impl.Adler32.fst code/Spec.Adler32.fst
TEST_FILE = code/c/test.c
KRML_OUTPUT = $(OBJ_DIR)/$(NAME).krml

C_FILE = $(BUILD_DIR)/$(NAME).c
H_FILE = $(BUILD_DIR)/$(NAME).h
OBJECT = $(BUILD_DIR)/$(NAME).o
ARCHIVE = $(BUILD_DIR)/lib$(NAME).a

# Default target
# Generate archive
$(ARCHIVE): $(OBJECT)
	ar rcs $(ARCHIVE) $(OBJECT)

# Generate Object file .o
$(OBJECT): $(C_FILE)
	ccomp \
	-Wall \
	-Werror \
	-std=c11 \
	-c $(C_FILE) \
	-o $(OBJECT) 

# Generate C and H file from .krml
$(C_FILE) $(H_FILE): $(KRML_OUTPUT)
	krml \
	-skip-compilation \
	-skip-makefiles \
	-minimal \
	-bundle 'Impl.Adler32=Impl.Adler32,Spec.Adler32,FStar.*,LowStar.*[rename=$(NAME)]' \
	-drop Prims,C_Loops \
	-add-include '<stdint.h>' \
	-tmpdir $(BUILD_DIR) \
	-no-prefix Impl.Adler32 \
	$(KRML_OUTPUT) 

# Generate the .krml file from F* code
$(KRML_OUTPUT): $(FST_FILES)
	mkdir --parent $(OBJ_DIR)
	install -m 664 $(KRML_HOME)/krmllib/obj/* $(OBJ_DIR)
	fstar.exe \
	--codegen krml \
	--krmloutput $(KRML_OUTPUT) \
	--include $(FSTAR_HOME) \
	--include $(KRML_HOME)/krmllib \
	--cache_dir $(OBJ_DIR) \
	--cache_checked_modules \
	--already_cached 'Prims FStar LowStar C TestLib' \
	$(FST_FILES)

test: $(ARCHIVE) $(TEST_FILE) $(H_FILE)
	@gcc $(TEST_FILE) -I$(BUILD_DIR) -L$(BUILD_DIR) -l$(NAME) -z noexecstack -o $(BUILD_DIR)/test
	@$(BUILD_DIR)/test
	@rm $(BUILD_DIR)/test

# Clean up generated files
clean:
	rm -rf $(OBJ_DIR) $(BUILD_DIR)

run:
	@$(EXE_OUTPUT)	

# Phony targets
.PHONY: all clean
