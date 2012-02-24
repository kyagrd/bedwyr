RCP = rsync -vrLtOCz --delete --stats --exclude /Makefile --exclude /releases/ --exclude ".*.swp"
upload:
	$(RCP) . shell.gforge.inria.fr:/home/groups/slimmer/htdocs

%:
	$(RCP) . $@@shell.gforge.inria.fr:/home/groups/slimmer/htdocs
