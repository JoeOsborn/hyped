#!/bin/bash

Z3_PATH_DEFAULT=/usr/local/Cellar/z3/HEAD-e0066df/lib/python2.7/

echo "Be sure to have virtualenv and virtualenvwrapper installed before proceeding, maybe via Python 2's pip."
echo "Also make sure you have Z3 installed (manually or via e.g. Homebrew on Mac OS X) and you have your Z3 Python bindings path handy!"
read -p "Z3 Python path? [$Z3_PATH_DEFAULT] " Z3_PATH
if [[ -z "$Z3_PATH" ]]; then
    Z3_PATH=$Z3_PATH_DEFAULT
fi
mkvirtualenv -p python2.7 hyped
pip install sympy scipy pygame rpython defusedxml value matplotlib jupyter
rm $VIRTUAL_ENV/bin/postactivate
cat <<EOF > postactivate
#!/bin/bash
export PYTHON_PATH=$Z3_PATH
EOF
chmod +x postactivate
ln -s postactivate $VIRTUAL_ENV/bin/postactivate
