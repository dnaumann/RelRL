# This makefile will run the makefile in all the examples in this directory
# including examples in all descendant subdirectories. Each example should have
# its own makefile that can be run independently.


# 1. Setup Directories
# Set DIR=<path> to limit traversal to that subtree, e.g. `make replay DIR=all_all`.
DIR ?= .
DIR := $(patsubst %/,%,$(DIR))

ifneq ($(DIR),.)
ifeq ($(wildcard $(DIR)/.),)
$(error DIR '$(DIR)' is not a directory)
endif
endif

# mindepth avoids this makefile when scanning from .
ifeq ($(DIR),.)
MAKEFILES := $(shell find . -mindepth 2 -name Makefile)
else
MAKEFILES := $(shell find "$(DIR)" -mindepth 1 -name Makefile)
endif
# Clean up SUBDIRS: remove ./ and trailing /
SUBDIRS   := $(patsubst %/,%,$(patsubst ./%,%,$(sort $(dir $(MAKEFILES)))))
RESULT_DIR := .build_results

# Define Colors
GREEN  := \033[1;32m
RED    := \033[1;31m
YELLOW := \033[1;33m
NC     := \033[0m # No Color


# Define a prefix for the standard build to avoid file conflicts
BUILD_TARGETS := $(addprefix build-,$(SUBDIRS))

# Define the replay targets based on subdirectories
REPLAY_TARGETS := $(addprefix replay-,$(SUBDIRS))


.PHONY: all replay clean summary $(BUILD_TARGETS) $(REPLAY_TARGETS)

# The 'all' target now calls specific build-prefix targets
all: $(BUILD_TARGETS)

# --- Rules ---

# The top-level replay target
replay: $(REPLAY_TARGETS)

# This rule uses the 'build-' prefix to stay unique
$(BUILD_TARGETS): build-%:
	@echo "== Building $* =="
	@$(MAKE) -C $*


# Replay with Banners and Result Tracking
$(REPLAY_TARGETS): replay-%:
	@mkdir -p $(RESULT_DIR)
	@printf '%s\n' '------------------------------------------'
	@printf '$(YELLOW)   Replaying: %s$(NC)\n' "$*"
	@printf '%s\n' '------------------------------------------'
	@start=$$(date +%s); \
	if $(MAKE) -C $* replay; then \
		elapsed=$$(( $$(date +%s) - start )); \
		printf '$(GREEN)   Time: %ds$(NC)\n' $$elapsed; \
		printf "$* : $(GREEN)SUCCESS$(NC) [%ds]\n" $$elapsed > $(RESULT_DIR)/$(subst /,_,$*).res; \
	else \
		elapsed=$$(( $$(date +%s) - start )); \
		printf '$(RED)   Time: %ds$(NC)\n' $$elapsed; \
		printf "$* : $(RED)FAILED$(NC) [%ds]\n" $$elapsed > $(RESULT_DIR)/$(subst /,_,$*).res; \
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

# Clean targets
CLEAN_TARGETS := $(addprefix clean-,$(SUBDIRS))
.PHONY: $(CLEAN_TARGETS)

clean: $(CLEAN_TARGETS)
	@rm -rf $(RESULT_DIR)

$(CLEAN_TARGETS): clean-%:
	@$(MAKE) -C $* clean


# make -j4 -k --output-sync=target replay
