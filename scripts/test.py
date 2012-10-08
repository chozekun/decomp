import glob
import os

try:
  os.mkdir('test_results')
except OSError:
  pass

for i in glob.glob('test/*.bin'):
  try:
    name, origin, entry, mmio, bin = i.split('.')
  except ValueError:
    name, bin = i.split('.')
    origin = 'default'
    entry = 'default'
    mmio = 'default'

  cmd = 'python3 decomp.py "' + i + '"'
  if origin != 'default':
    cmd += ' -o ' + origin
  if entry != 'default':
    cmd += ' -e ' + entry
  if mmio != 'default':
    cmd += ' -i ' + mmio
  cmd += ' >"' + i.replace('test/', 'test_results/').replace('.bin', '.log') + '" 2>&1'

  print(i.replace('test/', '') + ': ', end='')
  if os.system(cmd):
    print('FAIL')
  else:
    print('PASS')

