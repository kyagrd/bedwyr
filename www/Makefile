RCP = rsync -vrLtOCz --delete --stats \
      --exclude /Makefile --exclude /releases/ --exclude /doc/ --exclude /log/ \
      --exclude ".*.swp"

upload:
	$(RCP) . shell.gforge.inria.fr:/home/groups/slimmer/htdocs

%:
	$(RCP) . $@@shell.gforge.inria.fr:/home/groups/slimmer/htdocs
