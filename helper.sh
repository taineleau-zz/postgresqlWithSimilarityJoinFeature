cd $HOME/postgresql-build
../postgresql-src/configure --enable-depend --enable-cassert --enable-debug CFLAGS="-O0" --prefix=$HOME/pgsql
make && make install && cd .. && pg_ctl -D ./pgsql/data stop && rm -rf ./pgsql/data && mkdir ./pgsql/data &&  initdb -D ./pgsql/data --locale=C &&  pg_ctl -D ./pgsql/data -l logfile start && sleep 1
#if `psql` is called right after the server is started, it would return RE
psql postgres -c  'CREATE DATABASE similarity;' &&  psql -d similarity -f ./postgresql-src/similarity_data.sql