import glob
import os
from enum import Enum

empty_match_str = '''Provable and Useful in Completing Stuck Goal (Category 1)

Useful in Completing Stuck Goal (Category 2)

Valid Lemmas (Category 3)
'''

cat_1_str = "Provable and Useful in Completing Stuck Goal (Category 1)"
cat_2_str = "Useful in Completing Stuck Goal (Category 2)"
cat_3_str = "Valid Lemmas (Category 3)"

class FailureOptions(Enum):
  example = 'Failed Example Generation'
  other = 'Other Failure'

class ResultOption(Enum):
  fail = 'Failure'
  run = 'Run'
  success = 'Success'

class Result:
  def __init__(self, result, reason=None):
    self._result = result
    self._reason = reason

def is_solved(summary_log):
  # a file is solved if there are cat1
  pass

def split_context(content):
  from collections import Counter
  cnt = Counter
  import re
  return re.findall(f'(?<={cat_1_str})(.*?)(?={cat_2_str})', content, flags=re.S)

def read_run_results(prelude, benchmark):
  results = {}
  subdirs = [x for x in os.listdir(prelude) if x.startswith(f'_lfind_{benchmark}')]
  total = 0
  run = 0
  success = 0
  examples = 0
  empty_match = 0

  for subdir in subdirs:
    total += 1
    if not os.path.isfile(os.path.join(prelude, subdir, 'lfind_summary_log.txt')):
      if not glob.glob(prelude + '/' + subdir + '/examples*'):
      # if os.path.isfile(os.path.join(prelude, subdir, 'lfind_quickchick_generator.v')):
        results[subdir] = Result(ResultOption.fail, FailureOptions.example)
        examples += 1
      else:
        results[subdir] = Result(ResultOption.fail, FailureOptions.other)
    else:
      run += 1
      context = open(os.path.join(prelude, subdir, 'lfind_summary_log.txt')).read()
      # parsed_context = split_context(context)
      if empty_match_str in context:
        empty_match += 1
        # print("empty match")
        # total -= 1
        # success -= 1
        pass
      # elif 'Provable and Useful in Completing Stuck Goal (Category 1)' in context:
      else:
        results[subdir] = Result(ResultOption.success)
        success += 1
      results[subdir] = Result(ResultOption.run)
      # print(f'{subdir} runs successfully')


  print(f'{examples} runs failed due to example generation')
  print(f'{run}/{total} runs completed')
  print(f'{empty_match}/{total} runs return empty match')
  print(f'{success}/{total} runs successfully')
  return subdirs

print("old run")
old_run = read_run_results('/data/yousef/lfind/old_results/clam', 'clam')
print("new run")
new_run = read_run_results('/data/yousef/lfind/lemmafinder/benchmark', 'clam')

