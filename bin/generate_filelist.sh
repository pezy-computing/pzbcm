#!/bin/bash

filelist=${1}
path=`git rev-parse --show-toplevel`
if [ $# -ge 2 ]; then
  path=${2}
fi

bundle exec flgen --no-print-header --out ${filelist} ${path}/pzbcm.list.rb ${path}/pzcorebus.list.rb ${path}/pzhsbus.list.rb ${path}/pzvbus.list.rb
sed -i 's|'"${path}"'|${PZBCM_HOME}|g' ${filelist}
