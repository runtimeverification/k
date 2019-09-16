#!/usr/bin/python3
import glob
import os
import sys
import time

if len(sys.argv) < 4:
  print("usage: " + sys.argv[0] + " <kompiled-dir>... -- <files>...")
  exit(1)
allRules = set()
coverMap = {}

def addCover(rule):
  rule = rule.strip()
  if not rule in coverMap:
    coverMap[rule] = 0
  coverMap[rule] += 1

for idx, dir in enumerate(sys.argv[1:], start=1):
  if dir == "--":
    fileIdx = idx + 1
    break
  filename = dir + "/allRules.txt"
  with open(filename) as f:
    allRules.update(f.readlines())
  filename = dir + "/coverage.txt"
  with open(filename) as f:
    for line in f:
      addCover(line)
  for filename in glob.glob(dir + "/*_coverage.txt"):
    with open(filename) as f:
      for line in f:
        addCover(line)

sources = [os.path.abspath(path) for path in  sys.argv[fileIdx:]]

ruleMap = {}

for line in allRules:
  parts = line.split(" ")
  id = parts[0].strip()
  location = " ".join(parts[1:])
  parts = location.split(":")
  ruleMap[id] = (os.path.abspath(":".join(parts[:-2])), parts[-2], parts[-1])

allLines = set()

for key, value in ruleMap.items():
  allLines.add((value[0], value[1]))

def linesCovered(coverageOfComponent):
  coveredLines = set()
  for ruleId in coverageOfComponent:
    rule = ruleMap[ruleId]
    coveredLines.add((rule[0], rule[1]))
  return len(coveredLines)

def rulesCovered(coverageOfComponent):
  return len(coverageOfComponent)

numRulesGlobal = len(allRules)
numLines = len(allLines)
lineRateGlobal = float(linesCovered(coverMap)) / numLines
ruleRateGlobal = float(rulesCovered(coverMap)) / numRulesGlobal
timestamp = int(time.time())

template = """
<coverage line-rate="{lineRate}" branch-rate="{ruleRate}" version="1.9" timestamp="{timestamp}">
  <sources>
    <source>{source}</source>
  </sources>
  <packages>
    <package name="" line-rate="{lineRate}" branch-rate="{ruleRate}" complexity="{numRules}.0">
      <classes>
        {classesElem}
      </classes>
    </package>
  </packages>
</coverage>
"""

source = os.path.dirname(os.path.commonprefix(sources))

classTemplate = """
<class name="{filename}" filename="{filename}" line-rate="{lineRate}" branch-rate="{ruleRate}" complexity="{numRules}.0">
  <lines>
    {linesElem}
  </lines>
</class>
"""

lineTemplateNoBranch = """
<line number="{lineNum}" hits="{hits}" branch="false"/>
"""

lineTemplateBranch = """
<line number="{lineNum}" hits="{hits}" branch="true" condition-coverage="{ruleRate}% ({rulesCovered}/{numRules})">
  <conditions>
    <condition number="0" type="jump" coverage="{ruleRate}%"/>
  </conditions>
</line>
"""

ruleMapByFile = {}

for id, loc in ruleMap.items():
  if not loc[0] in ruleMapByFile:
    ruleMapByFile[loc[0]] = {}
  fileMap = ruleMapByFile[loc[0]]
  fileMap[id] = (loc[1], loc[2])

classes = []

for filename in sources:
  if not filename in ruleMapByFile:
    continue

  relativeFile = os.path.relpath(filename, source)
  allLines = set()

  allRules = ruleMapByFile[filename]
  ruleMapByLine = {}
  for key, value in allRules.items():
    allLines.add((value[0], value[1]))
    if not value[0] in ruleMapByLine:
      ruleMapByLine[value[0]] = [key]
    else:
      ruleMapByLine[value[0]].append(key)

  fileCoverage = {rule: num for rule, num in coverMap.items() if rule in allRules}

  numRulesFile = len(allRules)
  numLines = len(allLines)
  lineRateFile = float(linesCovered(fileCoverage)) / numLines
  ruleRateFile = float(rulesCovered(fileCoverage)) / numRulesFile
  
  lines = []

  for lineNum,rules in ruleMapByLine.items():
    lineCoverage = {rule: num for rule, num in fileCoverage.items() if rule in rules}
    hits = sum(lineCoverage.values())
    numCovered = len(lineCoverage)
    numRulesLine = len(rules)
    ruleRateLine = float(numCovered) / numRulesLine
    if numRulesLine == 1:
      lines.append(lineTemplateNoBranch.format(lineNum=lineNum,hits=hits))
    else:
      lines.append(lineTemplateBranch.format(lineNum=lineNum,hits=hits,ruleRate=int(ruleRateLine*100),rulesCovered=numCovered,numRules=numRulesLine))
  linesElem = "".join(lines)
  classes.append(classTemplate.format(filename=relativeFile,lineRate=lineRateFile,ruleRate=ruleRateFile,numRules=numRulesFile,linesElem=linesElem))

classesElem = "".join(classes)
xml = template.format(lineRate=lineRateGlobal,ruleRate=ruleRateGlobal,timestamp=timestamp,numRules=numRulesGlobal,source=source,classesElem=classesElem)
print(xml)
