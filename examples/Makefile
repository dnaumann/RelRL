# This makefile will run the makefile in all the examples in this directory
# including examples in all descendant subdirectories. Each example should have
# its own makefile that can be run independently.


# 1. Setup Directories
# mindepth to avoid this makefile
MAKEFILES := $(shell find . -mindepth 2 -name Makefile)
SUBDIRS   := $(sort $(dir $(MAKEFILES)))
RESULT_DIR := .build_results

# Define Colors
GREEN  := \033[1;32m
RED    := \033[1;31m
YELLOW := \033[1;33m
NC     := \033[0m # No Color


# Define a prefix for the standard build to avoid file conflicts
BUILD_TARGETS := $(addprefix build-,$(SUBDIRS))

.PHONY: all replay clean $(SUBDIRS) $(BUILD_TARGETS) summary

# The 'all' target now calls specific build-prefix targets
all: $(BUILD_TARGETS)

# --- Rules ---

# This rule uses the 'build-' prefix to stay unique
build-%:
	@echo "== Building $* =="
	@$(MAKE) -C $*


# Replay with Banners and Result Tracking
%.replay:
	@mkdir -p $(RESULT_DIR)
	@printf '%s\n' '------------------------------------------'
	@printf '$(YELLOW)--- Replaying: %s$(NC)\n' "$*"
	@printf '%s\n' '------------------------------------------'
	@if $(MAKE) -C $* replay; then \
		printf "$* : $(GREEN)SUCCESS$(NC)\n" > $(RESULT_DIR)/$(subst /,_,$*).res; \
	else \
		printf "$* : $(RED)FAILED$(NC)\n" > $(RESULT_DIR)/$(subst /,_,$*).res; \
	fi

# The Summary Reporter
summary:
	@echo ""
	@echo "=========================================="
	@echo "             REPLAY SUMMARY               "
	@echo "=========================================="
	@if [ -d $(RESULT_DIR) ]; then \
		cat $(RESULT_DIR)/*.res; \
		echo "------------------------------------------"; \
		printf "Total: "; ls $(RESULT_DIR)/*.res | wc -l; \
		printf "$(RED)Failed: $(NC)"; grep -l "FAILED" $(RESULT_DIR)/*.res 2>/dev/null | wc -l; \
		rm -rf $(RESULT_DIR); \
	else \
		echo "No results found."; \
	fi
	@echo "=========================================="

clean: $(addsuffix .clean,$(SUBDIRS))
	@rm -rf $(RESULT_DIR)

%.clean:
	@$(MAKE) -C $* clean


# make -j4 -k --output-sync=target replay