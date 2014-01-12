CREATE TABLE single_test_runs (
  id integer primary key autoincrement
  , test_id text references test_cases(filepath)
  , batch_id integer references test_batch_runs(id)
  , status text
  , stdout text
  , stderr text
  );
CREATE TABLE test_batch_runs (
  id integer primary key autoincrement
  , time integer
  , implementation text
  , impl_path text
  , impl_version text
  , title text
  , notes text
  , timestamp integer
  , system text
  , osnodename text
  , osrelease text
  , osversion text
  , hardware text
  );
CREATE TABLE test_cases (
  filepath text primary key
  , negative integer
  );
CREATE TABLE test_group_memberships (
  group_id integer references test_groups(id)
  , test_id integer references test_cases(filepath)
  );
CREATE TABLE test_groups (
  id integer primary key autoincrement
  , description text
  );
CREATE TABLE fail_group_memberships (
  group_id integer references test_groups(id)
  , test_id integer references test_cases(filepath)
  );
CREATE TABLE fail_groups (
  id integer primary key autoincrement
  , description text
  , reason text
  );

