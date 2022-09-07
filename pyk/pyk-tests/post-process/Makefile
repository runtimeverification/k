KOMPILED_DIR := kompiled

.PHONY: clean


$(KOMPILED_DIR)/timestamp: assign.k transform.py
	kompile assign.k                      \
	  --backend haskell                   \
	  --output-definition $(KOMPILED_DIR) \
	  --emit-json                         \
	  --post-process 'python3 transform.py'

clean:
	rm -rf $(KOMPILED_DIR)
