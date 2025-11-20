# This makefile will run the makefile in all the examples in this directory
# including examples in all descendant subdirectories. Each example should have
# its own makefile that can be run independently.

EXAMPLES := $(shell find . -name Makefile) 

# remove the current directory's makefile from the list
EXAMPLES := $(filter-out ./Makefile, $(EXAMPLES))

all: $(EXAMPLES)
	for dir in $(dir $(EXAMPLES)); do \
		$(MAKE) -C $$dir; \
	done

.PHONY: all $(EXAMPLES)
clean:
	for dir in $(dir $(EXAMPLES)); do \
		$(MAKE) -C $$dir clean; \
	done	
