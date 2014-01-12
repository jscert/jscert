#!/bin/bash
if [ -e test_results.db ]; then
   echo "Looks like test_results.db already exists"
   exit 1;
fi

cat createTestDB.sql | sqlite3 test_results.db;
cd ..
./test_data/make_ignorable_groups.sh
