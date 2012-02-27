all:
ifndef K_BASE
	@echo "K_BASE is not set. Maybe you are running make through sudo? Aborting.";
	@exit 2;
endif	
	@make -C core/java
	@make -C tools/krun


