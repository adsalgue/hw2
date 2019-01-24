######################################################
ORG=ucsd-cse230-wi19
ASGN=hw2
######################################################

hw2: deps src/Hw2.hs 
	stack exec -- liquid -i src src/Hw2.hs 

deps: src/ProofCombinators.hs 
	stack exec -- liquid src/ProofCombinators.hs

tags:
	hasktags -x -c src/

turnin: 
	git commit -a -m "turnin"
	git push origin master

upstream:
	git remote add upstream git@github.com:$(ORG)/$(ASGN).git

update:
	git pull upstream master
