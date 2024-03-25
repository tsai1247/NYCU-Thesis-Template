xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
bibtex main.aux
xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
xelatex -synctex=1 -shell-escape -interaction=nonstopmode main.tex
del *.aux 
del *.log 
del *.gz 
del *.bbl 
del *.blg 
del *.lof 
del *.lot 
del *.toc 
del *.out

