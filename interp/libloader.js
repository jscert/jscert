// Allow Test262 tests to include the things they like to include
var SafeEval = eval;
var t262Libs = {};
var $INCLUDE = function(lib) { SafeEval(t262Libs[lib]); };
t262Libs["Date_constants.js"] = "";
t262Libs["Date_library.js"] = "";
t262Libs["cth.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
function testRun(id, path, description, codeString, result, error) {\
  if (result!==\"pass\") {\
      throw new Error(\"Test '\" + path + \"'failed: \" + error);\
  }\
}\
\
function testFinished() {\
    //no-op\
}\
";
t262Libs["ed.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
//Error Detector\
if (this.window!==undefined) {  //for console support\
    this.window.onerror = function(errorMsg, url, lineNumber) {\
        this.window.iframeError = errorMsg;\
    };\
}\
\
//This doesn't work with early errors in current versions of Opera\
/*\
if (/opera/i.test(navigator.userAgent)) {\
    (function() {\
        var origError = window.Error;\
        window.Error = function() {\
            if (arguments.length>0) {\
                try {\
                    window.onerror(arguments[0]);\
                } catch(e) {\
                    alert(\"Failed to invoke window.onerror (from ed.js)\");\
                }\
            }\
            return origError.apply(this, arguments);\
        }\
    })();\
}*/\
";
t262Libs["environment.js"] = "";
t262Libs["framework.js"] = "// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function Test262Error(message) {\
  this.message = message;\
}\
\
Test262Error.prototype.toString = function () {\
  return \"Test262 Error: \" + this.message;\
};\
\
function testFailed(message) {\
  throw new Test262Error(message);\
}\
\
function testPrint(message) {\
\
}\
\
/**\
 * It is not yet clear that runTestCase should pass the global object\
 * as the 'this' binding in the call to testcase.\
 */\
var runTestCase = (function(global) {\
  return function(testcase) {\
    if (!testcase.call(global)) {\
      testFailed('test function returned falsy');\
    }\
  };\
})(this);\
\
function assertTruthy(value) {\
  if (!value) {\
    testFailed('test return falsy');\
  }\
}\
\
\
/**\
 * falsy means we expect no error.\
 * truthy means we expect some error.\
 * A non-empty string means we expect an error whose .name is that string.\
 */\
var expectedErrorName = false;\
\
/**\
 * What was thrown, or the string 'Falsy' if something falsy was thrown.\
 * null if test completed normally.\
 */\
var actualError = null;\
\
function testStarted(expectedErrName) {\
  expectedErrorName = expectedErrName;\
}\
\
function testFinished() {\
  var actualErrorName = actualError && (actualError.name ||\
                                        'SomethingThrown');\
  if (actualErrorName) {\
    if (expectedErrorName) {\
      if (typeof expectedErrorName === 'string') {\
        if (expectedErrorName === actualErrorName) {\
          return;\
        }\
        testFailed('Threw ' + actualErrorName +\
                   ' instead of ' + expectedErrorName);\
      }\
      return;\
    }\
    throw actualError;\
  }\
  if (expectedErrorName) {\
    if (typeof expectedErrorName === 'string') {\
      testFailed('Completed instead of throwing ' +\
                 expectedErrorName);\
    }\
    testFailed('Completed instead of throwing');\
  }\
}\
";
t262Libs["gs.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
//Global Scope Test Case Validator\
\
//An exception is expected\
if (testDescrip.negative !== undefined) {\
    //TODO - come up with a generic way of catching the error type\
    //from this.onerror\
    testDescrip.negative = testDescrip.negative === \"NotEarlyError\" ?\
            testDescrip.negative :\
        (testDescrip.negative === \"^((?!NotEarlyError).)*$\" ?\
            testDescrip.negative : \".\");\
    if (this.iframeError === undefined) { //no exception was thrown\
        testRun(testDescrip.id,\
                testDescrip.path,\
                testDescrip.description,\
                testDescrip.code,\
                'fail',\
                Error('No exception was thrown; expected an error \"message\"' +\
                      ' property matching the regular expression \"' +\
                      testDescrip.negative + '\".'));\
    } else if (!(new RegExp(testDescrip.negative,\
                            \"i\").test(this.iframeError))) {\
        //wrong type of exception thrown\
        testRun(testDescrip.id,\
                testDescrip.path,\
                testDescrip.description,\
                testDescrip.code,\
                'fail',\
                Error('Expected an exception with a \"message\"' +\
                      ' property matching the regular expression \"' +\
                      testDescrip.negative +\
                      '\" to be thrown; actual was \"' +\
                      this.iframeError + '\".'));\
    } else {\
        testRun(testDescrip.id,\
                testDescrip.path,\
                testDescrip.description,\
                testDescrip.code,\
                'pass',\
                undefined);\
    }\
}\
\
//Exception was not expected to be thrown\
else if (this.iframeError !== undefined) {\
    testRun(testDescrip.id,\
            testDescrip.path,\
            testDescrip.description,\
            testDescrip.code,\
            'fail',\
            Error('Unexpected exception, \"' +\
                  this.iframeError + '\" was thrown.'));\
}\
\
else {\
    testRun(testDescrip.id,\
            testDescrip.path,\
            testDescrip.description,\
            testDescrip.code,\
            'pass',\
            undefined);\
}\
\
testFinished();\
";
t262Libs["helper.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
/* Handles updating the page with information from the runner. */\
function Presenter() {\
    var altStyle = '',\
        logger,\
        date,\
        version,\
        table,\
        backLink,\
\
        globalSection = new Section(null, \"0\", STANDARD),\
        currentSection = globalSection,\
        tests = {},\
        totalTests = 0;\
\
    var progressBar;\
    TOCFILEPATH = \"metadata/\" + STANDARD.toLowerCase() + \"-toc.xml\";\
  //**INTERFACE****************************************************************\
  /* Updates progress with the given test, which should have its results in it as well. */\
    this.addTestResult = function(test) {\
        tests[test.id] = test;\
        getSectionById(test.id).addTest(test);\
\
        updateCounts();\
\
        //TODO: eventually remove this guard.\
        if(test.result === 'fail') {\
            logResult(test);\
        }\
    }\
    \
    /* Updates the displayed version. */\
    this.setVersion = function(v) {\
        version = v;\
        $(\".targetTestSuiteVersion\").text(v);\
    }\
    \
    /* Updates the displayed date. */\
    this.setDate = function(d) {\
        date = d;\
        $(\".targetTestSuiteDate\").text(d);\
    }\
    \
    /* Updates the displayed number of tests to run. */\
    this.setTotalTests = function(tests) {\
        totalTests = tests;\
        $('#testsToRun').text(tests);\
    }\
  \
    /* Write status to the activity bar. */\
    this.updateStatus = function (str) {\
       this.activityBar.text(str);\
    }\
    \
    /* When starting to load a test, create a table row entry and buttons. Display file path. */\
    this.setTestWaiting = function(index, path) {\
        var appendMsg = '<tr class=\"waiting\"><td height=\"29\" class=\"chapterName\">Waiting to load test file: ' + path + '</td>';\
        appendMsg += '<td width=\"83\"><img src=\"images/select.png\" alt=\"Select\" title=\"Toggle the selection of this chapter.\" /></td>';\
        appendMsg += '<td width=\"83\"><img src=\"images/run.png\" alt=\"Run\" title=\"Run this chapter individually.\" /></td></tr>';\
    \
        $('#chapterSelector table').append(appendMsg);\
        // Find the table row\
        var tr = $('#chapterSelector table tr').filter(\":last-child\");\
        \
        // Attach click listeners to the buttons\
        tr.find(\"img\").filter('[alt=\"Select\"]').bind(\"click\", {tr: tr, index: index}, function(event) {\
            controller.toggleSelection(event.data.index);\
            // Deselect row\
            if(event.data.tr.hasClass(\"selectedChapter\")) {\
                event.data.tr.removeClass(\"selectedChapter\");\
                event.data.tr.find('img').filter('[alt=\"Selected\"]').attr({\
                    src: 'images/select.png',\
                    alt: 'Select'\
                });\
            }\
            // Select row\
            else {\
                event.data.tr.addClass(\"selectedChapter\");\
                event.data.tr.find('img').filter('[alt=\"Select\"]').attr({\
                    src: 'images/selected.png',\
                    alt: 'Selected'\
                });\
            }\
        });\
    }\
    \
    this.setTestLoading = function(index, path) {\
        var tr = $('#chapterSelector table tr').filter(\":nth-child(\" + (index+1) + \")\");\
        tr.removeClass(\"waiting\");\
        tr.addClass(\"loading\");\
        tr.find(\":first-child\").html(\"Loading test file: \" + path);\
    };\
    \
    /* On test loaded, display the chapter name and the number of tests */\
    this.setTestLoaded = function(index, name, numTests) {\
        var tr = $('#chapterSelector table tr').filter(\":nth-child(\" + (index+1) + \")\");\
        tr.removeClass(\"loading\");\
        tr.find(\"td\").filter(\":first-child\").html(name + \" (\" + numTests + \" tests)\");\
    }\
    \
    /* Called when the tests finish executing. */\
    this.finished = function(elapsed) {\
        progressBar.find(\".text\").html(\"Testing complete!\"); \
        if (isSiteDebugMode()) {\
            this.activityBar.text('Overall Execution Time: ' + elapsed + ' minutes');\
        } else {\
            this.activityBar.text('');\
        }\
    }\
\
    this.reset = function () {\
        globalSection.reset();\
        updateCounts();\
        this.activityBar.text('');\
        logger.empty();\
\
        currentSection = globalSection;\
        renderCurrentSection();\
    }\
  \
  \
    /* Do some setup tasks. */\
    this.setup = function() {\
        backLink = $('#backlinkDiv');\
        backLink.click(goBack);\
        table = $('.results-data-table');\
        \
        logger = $(\"#tableLogger\");\
        progressBar = $('#progressbar');\
        this.activityBar = $('#nextActivity');\
        \
        $('a.showSource', logger).live(\"click\", openSourceWindow);\
        $('a.showError', logger).live(\"click\", openErrorWindow);\
        $('#ancGenXMLReport').click(createXMLReportWindow);\
    }\
    \
    /* Refresh display of the report */\
    this.refresh = function() {\
        renderCurrentSection();\
    }\
    \
    /* The state machine for the button display. */\
    this.setState = function(state) {\
        // Hide all the buttons\
        $('.progressBarButtons img').addClass(\"hide\");\
        // Only show what is needed.\
        if(state == 'loading') {\
            $('#btnRunAll').removeClass('hide');\
            $('#btnRunSelected').removeClass('hide');\
        }\
        else if(state == 'paused') {\
            $('#btnResume').removeClass('hide');\
            $('#btnReset').removeClass('hide');\
        }\
        else if(state == 'running') {\
            $('#btnPause').removeClass('hide');\
        }\
        else if(state == 'loaded') {\
            $('#btnRunAll').removeClass('hide');\
            $('#btnRunSelected').removeClass('hide');\
        }\
    };\
    \
    //**IMPLEMENTATION DETAILS***************************************************\
\
    /* Renders the current section into the report window. */\
    function renderCurrentSection() {\
        renderBreadcrumbs();\
        if(globalSection.totalTests === 0) {\
            $('#resultMessage').show();\
        } else {\
            $('#resultMessage').hide();\
        }\
\
        $('.totalCases').text(currentSection.totalTests);\
        $('.passedCases').text(currentSection.totalPassed);\
        $('.failedCases').text(currentSection.totalFailed);\
        $('#failedToLoadCounterDetails').text(currentSection.totalFailedToLoad);\
        table.empty();\
        table.append(currentSection.toHTML());\
        // Observe section selection and show source links\
        $('a.section', table).click(sectionSelected);\
        $('a.showSource', table).click(openSourceWindow);\
    }\
\
    /* Opens a window with a test's source code. */\
    function openSourceWindow(e) {\
        var test = tests[e.target.href.match(/#(.+)$/)[1]],\
            popWnd = window.open(\"\", \"\", \"scrollbars=1, resizable=1\"),\
            innerHTML = '';\
\
        innerHTML += '<b>Test </b>';\
        innerHTML += '<b>' + test.id + '</b> <br /><br />\\n';\
\
        if (test.description) {\
            innerHTML += '<b>Description</b>';\
            innerHTML += '<pre>' +\
                test.description.replace(/</g, '&lt;').replace(/>/g, '&gt;') +\
                ' </pre>\\n';\
        }\
\
        innerHTML += '<br /><br /><br /><b>Testcase</b>';\
        innerHTML += '<pre>' + test.code + '</pre>\\n';\
\
        innerHTML += '<br /><b>Path</b>';\
        innerHTML += '<pre>' + test.path + '</pre>';\
        innerHTML += '<br /><a href=\"javascript:void(window.open(\\'http://hg.ecmascript.org/tests/test262/file/tip/test/suite'\
        innerHTML += test.path.replace(\"TestCases\", \"\") + '\\'));\">' + 'Hg source' + '</a> (might be newer than the testcase source shown above)\\n'\
        \
        popWnd.document.write(innerHTML);\
    }\
\
    /* Opens a window with a test's failure message. */\
    function openErrorWindow(e) {\
        var test = tests[e.target.href.match(/#(.+)$/)[1]],\
            popWnd = window.open(\"\", \"\", \"scrollbars=1, resizable=1\"),\
            innerHTML = '';\
\
        var bugDetails = \"\";\
        bugDetails    += \"DESCRIPTION\\n*Please insert your description here!*\\n\\n\";\
        bugDetails    += \"------------------\\n\";\
        bugDetails    += \"TEST:            \" + test.path + \"\\n\";\
        bugDetails    += \"SOURCE:          http://hg.ecmascript.org/tests/test262/file/tip/test/suite\" + test.path.replace(\"TestCases\", \"\") + \"\\n\";\
        bugDetails    += \"TEST SUITE DATE: \" + date + \"\\n\";\
        bugDetails    += \"PLATFORM:        \" + navigator.userAgent + \"\\n\";\
        bugDetails    += \"ERROR:           \" + test.error + \"\\n\\n\";\
\
        \
        var bugTemplate = 'https://bugs.ecmascript.org/enter_bug.cgi?product=Test262&amp;bug_severity=normal&amp;component=Tests&amp;short_desc=';\
        bugTemplate += encodeURIComponent('Invalid test? ' + test.id) + \"&amp;comment=\";\
        bugTemplate += encodeURIComponent(bugDetails);\
        \
        innerHTML += '<b>Test </b>';\
        innerHTML += '<b>' + test.id + '</b> <br /><br />\\n';\
\
        innerHTML += '<b>Failure</b>';\
        innerHTML += '<pre>' + test.error + '</pre>\\n';\
        \
        innerHTML += '<br /><br /><b>Testcase</b>';\
        innerHTML += '<pre>' + test.code + '</pre>\\n';\
        \
        innerHTML += '<br /><br /><b>Broken test?</b>';\
        innerHTML += '<p>If you have reason to believe the JavaScript engine being tested<br />\\n';\
        innerHTML += 'is actually OK and there\\'s instead something wrong with the test<br />\\n';\
        innerHTML += 'itself, please <a href=\"' + bugTemplate + '\" onclick=\"window.moveTo(0,0);window.resizeTo(screen.width, screen.height);\">file a bug.</a></p>\\n'\
        \
        popWnd.document.write(innerHTML);\
    }\
\
    /* Returns the section object for the specified section id\
     * (eg. \"7.1\" or \"15.4.4.12\").\
     */\
    function getSectionById(id) {\
        if(id == 0)\
            return globalSection;\
\
        var match = id.match(/\\d+|[A-F](?=\\.)/g);\
        var section = globalSection;\
\
        if (match === null)\
            return section;\
\
        for(var i = 0; i < match.length; i++) {\
            if(typeof section.subsections[match[i]] !== \"undefined\") {\
                section = section.subsections[match[i]];\
            } else {\
                break;\
            }\
        }\
        return section;\
    }\
\
    /* Update the page with current status */\
    function updateCounts() {\
        $('#Pass').text(globalSection.totalPassed);\
        $('#Fail').text(globalSection.totalFailed);\
        $('#totalCounter').text(globalSection.totalTests);\
        $('#failedToLoadCounter1').text(globalSection.totalFailedToLoad);\
        $('#failedToLoadCounter').text(globalSection.totalFailedToLoad);\
        progressBar.reportprogress(globalSection.totalTests, totalTests);\
    }\
\
    /* Append a result to the run page's result log. */\
    function logResult(test) {\
        var appendStr = \"\";\
        altStyle = (altStyle !== ' ') ? ' ' : 'alternate';\
        if (test.result===\"fail\") {\
            appendStr += '<tbody>';\
            appendStr += '<tr class=\\\"' + altStyle + '\\\">';\
            \
            appendStr += '<td width=\\\"20%\\\">';\
            appendStr += \"<a class='showSource' href='#\" + test.id + \"'>\";\
            appendStr += test.id + \"</a>\";\
            appendStr += '</td>';\
            \
            appendStr += '<td>' + test.description + '</td>';\
            \
            appendStr += '<td align=\"right\">';\
            appendStr += '<span class=\\\"Fail\\\">' + \"<a class='showError' href='#\" + test.id + \"'>\";\
            appendStr += 'Fail</a></span></td></tr></tbody>';\
        }\
        \
        else if (test.result===\"pass\") {\
           if  (! isSiteDebugMode()) { return;}\
            appendStr += '<tbody><tr class=\\\"' + altStyle + '\\\"><td width=\\\"20%\\\">';\
            appendStr += \"<a class='showSource' href='#\" + test.id + \"'>\";\
            appendStr += test.id + \"</a>\" + '</td><td>' + test.description;\
            appendStr += '</td><td align=\"right\"><span class=\\\"Fail\\\">';\
            appendStr += 'Pass</span></td></tr></tbody>';\
        }\
        else {\
            throw \"Result for '\" + test.id + \"' must either be 'pass' or 'fail', not '\" + test.result + \"'!\";\
        }\
    \
            \
        logger.append(appendStr);\
        logger.parent().attr(\"scrollTop\", logger.parent().attr(\"scrollHeight\"));\
    }\
    \
    \
    \
    //*************************************************************************\
    /* Go back to the previous section */\
    function goBack(e) {\
        e.preventDefault();\
\
        if(currentSection === globalSection)\
            return;\
\
        currentSection = currentSection.parentSection;\
\
        // Since users click directly on sub-chapters of the main chapters, don't go back to main\
        // chapters.\
        if(currentSection.parentSection === globalSection)\
            currentSection = globalSection;\
\
        renderCurrentSection();\
    }\
    \
    /* Load the table of contents xml to populate the sections. */\
    function loadSections() {\
        var sectionsLoader = new XMLHttpRequest();\
        sectionsLoader.open(\"GET\", TOCFILEPATH, false);\
        sectionsLoader.send();\
        var xmlDoc = sectionsLoader.responseXML;\
        var nodes = xmlDoc.documentElement.childNodes;\
\
        addSectionsFromXML(nodes, globalSection);\
    }\
\
\
    /* Recursively parses the TOC xml, producing nested sections. */\
    function addSectionsFromXML(nodes, parentSection){\
        var subsection;\
\
        for (var i = 0; i < nodes.length; i++) {\
            if (nodes[i].nodeName === \"sec\") {\
                subsection = new Section(parentSection, nodes[i].getAttribute('id'), nodes[i].getAttribute('name'));\
                parentSection.subsections[subsection.id.match(/\\d+$|[A-F]$/)] = subsection;\
                addSectionsFromXML(nodes[i].childNodes, subsection);\
            }\
        }\
    }\
    \
    /* Renders the breadcrumbs for report navigation. */\
    function renderBreadcrumbs() {\
        var container = $('div.crumbContainer div.crumbs');\
        var sectionChain = [];\
\
        var current = currentSection;\
\
        // Walk backwards until we reach the global section.\
        while(current !== globalSection && current.parentSection !== globalSection) {\
            sectionChain.push(current);\
            current = current.parentSection;\
        }\
\
        // Reverse the array since we want to print earlier sections first.\
        sectionChain.reverse();\
\
        // Empty any existing breadcrumbs.\
        container.empty();\
\
        // Static first link to go back to the root.\
        var link = $(\"<a href='#0' class='setBlack'>Test Sections &gt; </a>\");\
        link.bind('click', {sectionId: 0}, sectionSelected)\
        container.append(link);\
\
        for(var i = 0; i < sectionChain.length;i++) {\
            link = $(\"<a href='#\" + sectionChain[i].id + \"' class='setBlack'>\" + sectionChain[i].id + \": \" + sectionChain[i].name + \" &gt; </a>\");\
            link.bind('click', sectionSelected)\
            container.append(link);\
        }\
\
        // If we can go back, show the back link.\
        if(sectionChain.length > 0) {\
            backLink.show();\
        } else {\
            backLink.hide();\
        }\
    };\
    \
    /* Pops up a window with an xml dump of the results of a test. */\
    function createXMLReportWindow() {\
        var reportWindow; //window that will output the xml data\
        var xmlData;      //array instead of string concatenation\
        var dateNow;\
        var xml;  // stop condition of for loop stored in a local variable to improve performance\
\
        dateNow = new Date();\
\
        xml = '<testRun>\\r\\n' +\
              '<userAgent>' + window.navigator.userAgent + '</userAgent>\\r\\n' +\
              '<Date>' + dateNow.toDateString() + '</Date>\\r\\n' +\
              '<targetTestSuiteName>ECMAScript Test262 Site</targetTestSuiteName>\\r\\n' +\
              '<targetTestSuiteVersion>' + version + '</targetTestSuiteVersion>\\r\\n' +\
              '<targetTestSuiteDate>' + date + '</targetTestSuiteDate>\\r\\n' +\
              ' <Tests>\\r\\n\\r\\n';\
\
        reportWindow = window.open();\
        reportWindow.document.writeln(\"<title>ECMAScript Test262 XML</title>\");\
        reportWindow.document.write(\"<textarea id='results' style='width: 100%; height: 800px;'>\");\
        reportWindow.document.write(xml);\
        reportWindow.document.write(globalSection.toXML());\
        reportWindow.document.write('</Tests>\\r\\n</testRun>\\r\\n</textarea>\\r\\n');\
        reportWindow.document.close();\
    }\
\
    /* Callback for when the user clicks on a section in the report table. */\
    function sectionSelected(e) {\
        e.preventDefault();\
        currentSection = getSectionById(e.target.href.match(/#(.+)$/)[1]);\
        renderCurrentSection();\
        table.attr(\"scrollTop\", 0);\
    };\
    \
    //*************************************************************************\
    // Load the sections.\
    loadSections();\
}\
\
var presenter = new Presenter();\
";
t262Libs["jquery-1.4.2.min.js"] = "/*!\
 * jQuery JavaScript Library v1.4.2\
 * http://jquery.com/\
 *\
 * Copyright 2010, John Resig\
 * Dual licensed under the MIT or GPL Version 2 licenses.\
 * http://jquery.org/license\
 *\
 * Includes Sizzle.js\
 * http://sizzlejs.com/\
 * Copyright 2010, The Dojo Foundation\
 * Released under the MIT, BSD, and GPL Licenses.\
 *\
 * Date: Sat Feb 13 22:33:48 2010 -0500\
 */\
(function(A,w){function ma(){if(!c.isReady){try{s.documentElement.doScroll(\"left\")}catch(a){setTimeout(ma,1);return}c.ready()}}function Qa(a,b){b.src?c.ajax({url:b.src,async:false,dataType:\"script\"}):c.globalEval(b.text||b.textContent||b.innerHTML||\"\");b.parentNode&&b.parentNode.removeChild(b)}function X(a,b,d,f,e,j){var i=a.length;if(typeof b===\"object\"){for(var o in b)X(a,o,b[o],f,e,d);return a}if(d!==w){f=!j&&f&&c.isFunction(d);for(o=0;o<i;o++)e(a[o],b,f?d.call(a[o],o,e(a[o],b)):d,j);return a}return i?\
e(a[0],b):w}function J(){return(new Date).getTime()}function Y(){return false}function Z(){return true}function na(a,b,d){d[0].type=a;return c.event.handle.apply(b,d)}function oa(a){var b,d=[],f=[],e=arguments,j,i,o,k,n,r;i=c.data(this,\"events\");if(!(a.liveFired===this||!i||!i.live||a.button&&a.type===\"click\")){a.liveFired=this;var u=i.live.slice(0);for(k=0;k<u.length;k++){i=u[k];i.origType.replace(O,\"\")===a.type?f.push(i.selector):u.splice(k--,1)}j=c(a.target).closest(f,a.currentTarget);n=0;for(r=\
j.length;n<r;n++)for(k=0;k<u.length;k++){i=u[k];if(j[n].selector===i.selector){o=j[n].elem;f=null;if(i.preType===\"mouseenter\"||i.preType===\"mouseleave\")f=c(a.relatedTarget).closest(i.selector)[0];if(!f||f!==o)d.push({elem:o,handleObj:i})}}n=0;for(r=d.length;n<r;n++){j=d[n];a.currentTarget=j.elem;a.data=j.handleObj.data;a.handleObj=j.handleObj;if(j.handleObj.origHandler.apply(j.elem,e)===false){b=false;break}}return b}}function pa(a,b){return\"live.\"+(a&&a!==\"*\"?a+\".\":\"\")+b.replace(/\\./g,\"`\").replace(/ /g,\
\"&\")}function qa(a){return!a||!a.parentNode||a.parentNode.nodeType===11}function ra(a,b){var d=0;b.each(function(){if(this.nodeName===(a[d]&&a[d].nodeName)){var f=c.data(a[d++]),e=c.data(this,f);if(f=f&&f.events){delete e.handle;e.events={};for(var j in f)for(var i in f[j])c.event.add(this,j,f[j][i],f[j][i].data)}}})}function sa(a,b,d){var f,e,j;b=b&&b[0]?b[0].ownerDocument||b[0]:s;if(a.length===1&&typeof a[0]===\"string\"&&a[0].length<512&&b===s&&!ta.test(a[0])&&(c.support.checkClone||!ua.test(a[0]))){e=\
true;if(j=c.fragments[a[0]])if(j!==1)f=j}if(!f){f=b.createDocumentFragment();c.clean(a,b,f,d)}if(e)c.fragments[a[0]]=j?f:1;return{fragment:f,cacheable:e}}function K(a,b){var d={};c.each(va.concat.apply([],va.slice(0,b)),function(){d[this]=a});return d}function wa(a){return\"scrollTo\"in a&&a.document?a:a.nodeType===9?a.defaultView||a.parentWindow:false}var c=function(a,b){return new c.fn.init(a,b)},Ra=A.jQuery,Sa=A.$,s=A.document,T,Ta=/^[^<]*(<[\\w\\W]+>)[^>]*$|^#([\\w-]+)$/,Ua=/^.[^:#\\[\\.,]*$/,Va=/\\S/,\
Wa=/^(\\s|\\u00A0)+|(\\s|\\u00A0)+$/g,Xa=/^<(\\w+)\\s*\\/?>(?:<\\/\\1>)?$/,P=navigator.userAgent,xa=false,Q=[],L,$=Object.prototype.toString,aa=Object.prototype.hasOwnProperty,ba=Array.prototype.push,R=Array.prototype.slice,ya=Array.prototype.indexOf;c.fn=c.prototype={init:function(a,b){var d,f;if(!a)return this;if(a.nodeType){this.context=this[0]=a;this.length=1;return this}if(a===\"body\"&&!b){this.context=s;this[0]=s.body;this.selector=\"body\";this.length=1;return this}if(typeof a===\"string\")if((d=Ta.exec(a))&&\
(d[1]||!b))if(d[1]){f=b?b.ownerDocument||b:s;if(a=Xa.exec(a))if(c.isPlainObject(b)){a=[s.createElement(a[1])];c.fn.attr.call(a,b,true)}else a=[f.createElement(a[1])];else{a=sa([d[1]],[f]);a=(a.cacheable?a.fragment.cloneNode(true):a.fragment).childNodes}return c.merge(this,a)}else{if(b=s.getElementById(d[2])){if(b.id!==d[2])return T.find(a);this.length=1;this[0]=b}this.context=s;this.selector=a;return this}else if(!b&&/^\\w+$/.test(a)){this.selector=a;this.context=s;a=s.getElementsByTagName(a);return c.merge(this,\
a)}else return!b||b.jquery?(b||T).find(a):c(b).find(a);else if(c.isFunction(a))return T.ready(a);if(a.selector!==w){this.selector=a.selector;this.context=a.context}return c.makeArray(a,this)},selector:\"\",jquery:\"1.4.2\",length:0,size:function(){return this.length},toArray:function(){return R.call(this,0)},get:function(a){return a==null?this.toArray():a<0?this.slice(a)[0]:this[a]},pushStack:function(a,b,d){var f=c();c.isArray(a)?ba.apply(f,a):c.merge(f,a);f.prevObject=this;f.context=this.context;if(b===\
\"find\")f.selector=this.selector+(this.selector?\" \":\"\")+d;else if(b)f.selector=this.selector+\".\"+b+\"(\"+d+\")\";return f},each:function(a,b){return c.each(this,a,b)},ready:function(a){c.bindReady();if(c.isReady)a.call(s,c);else Q&&Q.push(a);return this},eq:function(a){return a===-1?this.slice(a):this.slice(a,+a+1)},first:function(){return this.eq(0)},last:function(){return this.eq(-1)},slice:function(){return this.pushStack(R.apply(this,arguments),\"slice\",R.call(arguments).join(\",\"))},map:function(a){return this.pushStack(c.map(this,\
function(b,d){return a.call(b,d,b)}))},end:function(){return this.prevObject||c(null)},push:ba,sort:[].sort,splice:[].splice};c.fn.init.prototype=c.fn;c.extend=c.fn.extend=function(){var a=arguments[0]||{},b=1,d=arguments.length,f=false,e,j,i,o;if(typeof a===\"boolean\"){f=a;a=arguments[1]||{};b=2}if(typeof a!==\"object\"&&!c.isFunction(a))a={};if(d===b){a=this;--b}for(;b<d;b++)if((e=arguments[b])!=null)for(j in e){i=a[j];o=e[j];if(a!==o)if(f&&o&&(c.isPlainObject(o)||c.isArray(o))){i=i&&(c.isPlainObject(i)||\
c.isArray(i))?i:c.isArray(o)?[]:{};a[j]=c.extend(f,i,o)}else if(o!==w)a[j]=o}return a};c.extend({noConflict:function(a){A.$=Sa;if(a)A.jQuery=Ra;return c},isReady:false,ready:function(){if(!c.isReady){if(!s.body)return setTimeout(c.ready,13);c.isReady=true;if(Q){for(var a,b=0;a=Q[b++];)a.call(s,c);Q=null}c.fn.triggerHandler&&c(s).triggerHandler(\"ready\")}},bindReady:function(){if(!xa){xa=true;if(s.readyState===\"complete\")return c.ready();if(s.addEventListener){s.addEventListener(\"DOMContentLoaded\",\
L,false);A.addEventListener(\"load\",c.ready,false)}else if(s.attachEvent){s.attachEvent(\"onreadystatechange\",L);A.attachEvent(\"onload\",c.ready);var a=false;try{a=A.frameElement==null}catch(b){}s.documentElement.doScroll&&a&&ma()}}},isFunction:function(a){return $.call(a)===\"[object Function]\"},isArray:function(a){return $.call(a)===\"[object Array]\"},isPlainObject:function(a){if(!a||$.call(a)!==\"[object Object]\"||a.nodeType||a.setInterval)return false;if(a.constructor&&!aa.call(a,\"constructor\")&&!aa.call(a.constructor.prototype,\
\"isPrototypeOf\"))return false;var b;for(b in a);return b===w||aa.call(a,b)},isEmptyObject:function(a){for(var b in a)return false;return true},error:function(a){throw a;},parseJSON:function(a){if(typeof a!==\"string\"||!a)return null;a=c.trim(a);if(/^[\\],:{}\\s]*$/.test(a.replace(/\\\\(?:[\"\\\\\\/bfnrt]|u[0-9a-fA-F]{4})/g,\"@\").replace(/\"[^\"\\\\\\n\\r]*\"|true|false|null|-?\\d+(?:\\.\\d*)?(?:[eE][+\\-]?\\d+)?/g,\"]\").replace(/(?:^|:|,)(?:\\s*\\[)+/g,\"\")))return A.JSON&&A.JSON.parse?A.JSON.parse(a):(new Function(\"return \"+\
a))();else c.error(\"Invalid JSON: \"+a)},noop:function(){},globalEval:function(a){if(a&&Va.test(a)){var b=s.getElementsByTagName(\"head\")[0]||s.documentElement,d=s.createElement(\"script\");d.type=\"text/javascript\";if(c.support.scriptEval)d.appendChild(s.createTextNode(a));else d.text=a;b.insertBefore(d,b.firstChild);b.removeChild(d)}},nodeName:function(a,b){return a.nodeName&&a.nodeName.toUpperCase()===b.toUpperCase()},each:function(a,b,d){var f,e=0,j=a.length,i=j===w||c.isFunction(a);if(d)if(i)for(f in a){if(b.apply(a[f],\
d)===false)break}else for(;e<j;){if(b.apply(a[e++],d)===false)break}else if(i)for(f in a){if(b.call(a[f],f,a[f])===false)break}else for(d=a[0];e<j&&b.call(d,e,d)!==false;d=a[++e]);return a},trim:function(a){return(a||\"\").replace(Wa,\"\")},makeArray:function(a,b){b=b||[];if(a!=null)a.length==null||typeof a===\"string\"||c.isFunction(a)||typeof a!==\"function\"&&a.setInterval?ba.call(b,a):c.merge(b,a);return b},inArray:function(a,b){if(b.indexOf)return b.indexOf(a);for(var d=0,f=b.length;d<f;d++)if(b[d]===\
a)return d;return-1},merge:function(a,b){var d=a.length,f=0;if(typeof b.length===\"number\")for(var e=b.length;f<e;f++)a[d++]=b[f];else for(;b[f]!==w;)a[d++]=b[f++];a.length=d;return a},grep:function(a,b,d){for(var f=[],e=0,j=a.length;e<j;e++)!d!==!b(a[e],e)&&f.push(a[e]);return f},map:function(a,b,d){for(var f=[],e,j=0,i=a.length;j<i;j++){e=b(a[j],j,d);if(e!=null)f[f.length]=e}return f.concat.apply([],f)},guid:1,proxy:function(a,b,d){if(arguments.length===2)if(typeof b===\"string\"){d=a;a=d[b];b=w}else if(b&&\
!c.isFunction(b)){d=b;b=w}if(!b&&a)b=function(){return a.apply(d||this,arguments)};if(a)b.guid=a.guid=a.guid||b.guid||c.guid++;return b},uaMatch:function(a){a=a.toLowerCase();a=/(webkit)[ \\/]([\\w.]+)/.exec(a)||/(opera)(?:.*version)?[ \\/]([\\w.]+)/.exec(a)||/(msie) ([\\w.]+)/.exec(a)||!/compatible/.test(a)&&/(mozilla)(?:.*? rv:([\\w.]+))?/.exec(a)||[];return{browser:a[1]||\"\",version:a[2]||\"0\"}},browser:{}});P=c.uaMatch(P);if(P.browser){c.browser[P.browser]=true;c.browser.version=P.version}if(c.browser.webkit)c.browser.safari=\
true;if(ya)c.inArray=function(a,b){return ya.call(b,a)};T=c(s);if(s.addEventListener)L=function(){s.removeEventListener(\"DOMContentLoaded\",L,false);c.ready()};else if(s.attachEvent)L=function(){if(s.readyState===\"complete\"){s.detachEvent(\"onreadystatechange\",L);c.ready()}};(function(){c.support={};var a=s.documentElement,b=s.createElement(\"script\"),d=s.createElement(\"div\"),f=\"script\"+J();d.style.display=\"none\";d.innerHTML=\"   <link/><table></table><a href='/a' style='color:red;float:left;opacity:.55;'>a</a><input type='checkbox'/>\";\
var e=d.getElementsByTagName(\"*\"),j=d.getElementsByTagName(\"a\")[0];if(!(!e||!e.length||!j)){c.support={leadingWhitespace:d.firstChild.nodeType===3,tbody:!d.getElementsByTagName(\"tbody\").length,htmlSerialize:!!d.getElementsByTagName(\"link\").length,style:/red/.test(j.getAttribute(\"style\")),hrefNormalized:j.getAttribute(\"href\")===\"/a\",opacity:/^0.55$/.test(j.style.opacity),cssFloat:!!j.style.cssFloat,checkOn:d.getElementsByTagName(\"input\")[0].value===\"on\",optSelected:s.createElement(\"select\").appendChild(s.createElement(\"option\")).selected,\
parentNode:d.removeChild(d.appendChild(s.createElement(\"div\"))).parentNode===null,deleteExpando:true,checkClone:false,scriptEval:false,noCloneEvent:true,boxModel:null};b.type=\"text/javascript\";try{b.appendChild(s.createTextNode(\"window.\"+f+\"=1;\"))}catch(i){}a.insertBefore(b,a.firstChild);if(A[f]){c.support.scriptEval=true;delete A[f]}try{delete b.test}catch(o){c.support.deleteExpando=false}a.removeChild(b);if(d.attachEvent&&d.fireEvent){d.attachEvent(\"onclick\",function k(){c.support.noCloneEvent=\
false;d.detachEvent(\"onclick\",k)});d.cloneNode(true).fireEvent(\"onclick\")}d=s.createElement(\"div\");d.innerHTML=\"<input type='radio' name='radiotest' checked='checked'/>\";a=s.createDocumentFragment();a.appendChild(d.firstChild);c.support.checkClone=a.cloneNode(true).cloneNode(true).lastChild.checked;c(function(){var k=s.createElement(\"div\");k.style.width=k.style.paddingLeft=\"1px\";s.body.appendChild(k);c.boxModel=c.support.boxModel=k.offsetWidth===2;s.body.removeChild(k).style.display=\"none\"});a=function(k){var n=\
s.createElement(\"div\");k=\"on\"+k;var r=k in n;if(!r){n.setAttribute(k,\"return;\");r=typeof n[k]===\"function\"}return r};c.support.submitBubbles=a(\"submit\");c.support.changeBubbles=a(\"change\");a=b=d=e=j=null}})();c.props={\"for\":\"htmlFor\",\"class\":\"className\",readonly:\"readOnly\",maxlength:\"maxLength\",cellspacing:\"cellSpacing\",rowspan:\"rowSpan\",colspan:\"colSpan\",tabindex:\"tabIndex\",usemap:\"useMap\",frameborder:\"frameBorder\"};var G=\"jQuery\"+J(),Ya=0,za={};c.extend({cache:{},expando:G,noData:{embed:true,object:true,\
applet:true},data:function(a,b,d){if(!(a.nodeName&&c.noData[a.nodeName.toLowerCase()])){a=a==A?za:a;var f=a[G],e=c.cache;if(!f&&typeof b===\"string\"&&d===w)return null;f||(f=++Ya);if(typeof b===\"object\"){a[G]=f;e[f]=c.extend(true,{},b)}else if(!e[f]){a[G]=f;e[f]={}}a=e[f];if(d!==w)a[b]=d;return typeof b===\"string\"?a[b]:a}},removeData:function(a,b){if(!(a.nodeName&&c.noData[a.nodeName.toLowerCase()])){a=a==A?za:a;var d=a[G],f=c.cache,e=f[d];if(b){if(e){delete e[b];c.isEmptyObject(e)&&c.removeData(a)}}else{if(c.support.deleteExpando)delete a[c.expando];\
else a.removeAttribute&&a.removeAttribute(c.expando);delete f[d]}}}});c.fn.extend({data:function(a,b){if(typeof a===\"undefined\"&&this.length)return c.data(this[0]);else if(typeof a===\"object\")return this.each(function(){c.data(this,a)});var d=a.split(\".\");d[1]=d[1]?\".\"+d[1]:\"\";if(b===w){var f=this.triggerHandler(\"getData\"+d[1]+\"!\",[d[0]]);if(f===w&&this.length)f=c.data(this[0],a);return f===w&&d[1]?this.data(d[0]):f}else return this.trigger(\"setData\"+d[1]+\"!\",[d[0],b]).each(function(){c.data(this,\
a,b)})},removeData:function(a){return this.each(function(){c.removeData(this,a)})}});c.extend({queue:function(a,b,d){if(a){b=(b||\"fx\")+\"queue\";var f=c.data(a,b);if(!d)return f||[];if(!f||c.isArray(d))f=c.data(a,b,c.makeArray(d));else f.push(d);return f}},dequeue:function(a,b){b=b||\"fx\";var d=c.queue(a,b),f=d.shift();if(f===\"inprogress\")f=d.shift();if(f){b===\"fx\"&&d.unshift(\"inprogress\");f.call(a,function(){c.dequeue(a,b)})}}});c.fn.extend({queue:function(a,b){if(typeof a!==\"string\"){b=a;a=\"fx\"}if(b===\
w)return c.queue(this[0],a);return this.each(function(){var d=c.queue(this,a,b);a===\"fx\"&&d[0]!==\"inprogress\"&&c.dequeue(this,a)})},dequeue:function(a){return this.each(function(){c.dequeue(this,a)})},delay:function(a,b){a=c.fx?c.fx.speeds[a]||a:a;b=b||\"fx\";return this.queue(b,function(){var d=this;setTimeout(function(){c.dequeue(d,b)},a)})},clearQueue:function(a){return this.queue(a||\"fx\",[])}});var Aa=/[\\n\\t]/g,ca=/\\s+/,Za=/\\r/g,$a=/href|src|style/,ab=/(button|input)/i,bb=/(button|input|object|select|textarea)/i,\
cb=/^(a|area)$/i,Ba=/radio|checkbox/;c.fn.extend({attr:function(a,b){return X(this,a,b,true,c.attr)},removeAttr:function(a){return this.each(function(){c.attr(this,a,\"\");this.nodeType===1&&this.removeAttribute(a)})},addClass:function(a){if(c.isFunction(a))return this.each(function(n){var r=c(this);r.addClass(a.call(this,n,r.attr(\"class\")))});if(a&&typeof a===\"string\")for(var b=(a||\"\").split(ca),d=0,f=this.length;d<f;d++){var e=this[d];if(e.nodeType===1)if(e.className){for(var j=\" \"+e.className+\" \",\
i=e.className,o=0,k=b.length;o<k;o++)if(j.indexOf(\" \"+b[o]+\" \")<0)i+=\" \"+b[o];e.className=c.trim(i)}else e.className=a}return this},removeClass:function(a){if(c.isFunction(a))return this.each(function(k){var n=c(this);n.removeClass(a.call(this,k,n.attr(\"class\")))});if(a&&typeof a===\"string\"||a===w)for(var b=(a||\"\").split(ca),d=0,f=this.length;d<f;d++){var e=this[d];if(e.nodeType===1&&e.className)if(a){for(var j=(\" \"+e.className+\" \").replace(Aa,\" \"),i=0,o=b.length;i<o;i++)j=j.replace(\" \"+b[i]+\" \",\
\" \");e.className=c.trim(j)}else e.className=\"\"}return this},toggleClass:function(a,b){var d=typeof a,f=typeof b===\"boolean\";if(c.isFunction(a))return this.each(function(e){var j=c(this);j.toggleClass(a.call(this,e,j.attr(\"class\"),b),b)});return this.each(function(){if(d===\"string\")for(var e,j=0,i=c(this),o=b,k=a.split(ca);e=k[j++];){o=f?o:!i.hasClass(e);i[o?\"addClass\":\"removeClass\"](e)}else if(d===\"undefined\"||d===\"boolean\"){this.className&&c.data(this,\"__className__\",this.className);this.className=\
this.className||a===false?\"\":c.data(this,\"__className__\")||\"\"}})},hasClass:function(a){a=\" \"+a+\" \";for(var b=0,d=this.length;b<d;b++)if((\" \"+this[b].className+\" \").replace(Aa,\" \").indexOf(a)>-1)return true;return false},val:function(a){if(a===w){var b=this[0];if(b){if(c.nodeName(b,\"option\"))return(b.attributes.value||{}).specified?b.value:b.text;if(c.nodeName(b,\"select\")){var d=b.selectedIndex,f=[],e=b.options;b=b.type===\"select-one\";if(d<0)return null;var j=b?d:0;for(d=b?d+1:e.length;j<d;j++){var i=\
e[j];if(i.selected){a=c(i).val();if(b)return a;f.push(a)}}return f}if(Ba.test(b.type)&&!c.support.checkOn)return b.getAttribute(\"value\")===null?\"on\":b.value;return(b.value||\"\").replace(Za,\"\")}return w}var o=c.isFunction(a);return this.each(function(k){var n=c(this),r=a;if(this.nodeType===1){if(o)r=a.call(this,k,n.val());if(typeof r===\"number\")r+=\"\";if(c.isArray(r)&&Ba.test(this.type))this.checked=c.inArray(n.val(),r)>=0;else if(c.nodeName(this,\"select\")){var u=c.makeArray(r);c(\"option\",this).each(function(){this.selected=\
c.inArray(c(this).val(),u)>=0});if(!u.length)this.selectedIndex=-1}else this.value=r}})}});c.extend({attrFn:{val:true,css:true,html:true,text:true,data:true,width:true,height:true,offset:true},attr:function(a,b,d,f){if(!a||a.nodeType===3||a.nodeType===8)return w;if(f&&b in c.attrFn)return c(a)[b](d);f=a.nodeType!==1||!c.isXMLDoc(a);var e=d!==w;b=f&&c.props[b]||b;if(a.nodeType===1){var j=$a.test(b);if(b in a&&f&&!j){if(e){b===\"type\"&&ab.test(a.nodeName)&&a.parentNode&&c.error(\"type property can't be changed\");\
a[b]=d}if(c.nodeName(a,\"form\")&&a.getAttributeNode(b))return a.getAttributeNode(b).nodeValue;if(b===\"tabIndex\")return(b=a.getAttributeNode(\"tabIndex\"))&&b.specified?b.value:bb.test(a.nodeName)||cb.test(a.nodeName)&&a.href?0:w;return a[b]}if(!c.support.style&&f&&b===\"style\"){if(e)a.style.cssText=\"\"+d;return a.style.cssText}e&&a.setAttribute(b,\"\"+d);a=!c.support.hrefNormalized&&f&&j?a.getAttribute(b,2):a.getAttribute(b);return a===null?w:a}return c.style(a,b,d)}});var O=/\\.(.*)$/,db=function(a){return a.replace(/[^\\w\\s\\.\\|`]/g,\
function(b){return\"\\\\\"+b})};c.event={add:function(a,b,d,f){if(!(a.nodeType===3||a.nodeType===8)){if(a.setInterval&&a!==A&&!a.frameElement)a=A;var e,j;if(d.handler){e=d;d=e.handler}if(!d.guid)d.guid=c.guid++;if(j=c.data(a)){var i=j.events=j.events||{},o=j.handle;if(!o)j.handle=o=function(){return typeof c!==\"undefined\"&&!c.event.triggered?c.event.handle.apply(o.elem,arguments):w};o.elem=a;b=b.split(\" \");for(var k,n=0,r;k=b[n++];){j=e?c.extend({},e):{handler:d,data:f};if(k.indexOf(\".\")>-1){r=k.split(\".\");\
k=r.shift();j.namespace=r.slice(0).sort().join(\".\")}else{r=[];j.namespace=\"\"}j.type=k;j.guid=d.guid;var u=i[k],z=c.event.special[k]||{};if(!u){u=i[k]=[];if(!z.setup||z.setup.call(a,f,r,o)===false)if(a.addEventListener)a.addEventListener(k,o,false);else a.attachEvent&&a.attachEvent(\"on\"+k,o)}if(z.add){z.add.call(a,j);if(!j.handler.guid)j.handler.guid=d.guid}u.push(j);c.event.global[k]=true}a=null}}},global:{},remove:function(a,b,d,f){if(!(a.nodeType===3||a.nodeType===8)){var e,j=0,i,o,k,n,r,u,z=c.data(a),\
C=z&&z.events;if(z&&C){if(b&&b.type){d=b.handler;b=b.type}if(!b||typeof b===\"string\"&&b.charAt(0)===\".\"){b=b||\"\";for(e in C)c.event.remove(a,e+b)}else{for(b=b.split(\" \");e=b[j++];){n=e;i=e.indexOf(\".\")<0;o=[];if(!i){o=e.split(\".\");e=o.shift();k=new RegExp(\"(^|\\\\.)\"+c.map(o.slice(0).sort(),db).join(\"\\\\.(?:.*\\\\.)?\")+\"(\\\\.|$)\")}if(r=C[e])if(d){n=c.event.special[e]||{};for(B=f||0;B<r.length;B++){u=r[B];if(d.guid===u.guid){if(i||k.test(u.namespace)){f==null&&r.splice(B--,1);n.remove&&n.remove.call(a,u)}if(f!=\
null)break}}if(r.length===0||f!=null&&r.length===1){if(!n.teardown||n.teardown.call(a,o)===false)Ca(a,e,z.handle);delete C[e]}}else for(var B=0;B<r.length;B++){u=r[B];if(i||k.test(u.namespace)){c.event.remove(a,n,u.handler,B);r.splice(B--,1)}}}if(c.isEmptyObject(C)){if(b=z.handle)b.elem=null;delete z.events;delete z.handle;c.isEmptyObject(z)&&c.removeData(a)}}}}},trigger:function(a,b,d,f){var e=a.type||a;if(!f){a=typeof a===\"object\"?a[G]?a:c.extend(c.Event(e),a):c.Event(e);if(e.indexOf(\"!\")>=0){a.type=\
e=e.slice(0,-1);a.exclusive=true}if(!d){a.stopPropagation();c.event.global[e]&&c.each(c.cache,function(){this.events&&this.events[e]&&c.event.trigger(a,b,this.handle.elem)})}if(!d||d.nodeType===3||d.nodeType===8)return w;a.result=w;a.target=d;b=c.makeArray(b);b.unshift(a)}a.currentTarget=d;(f=c.data(d,\"handle\"))&&f.apply(d,b);f=d.parentNode||d.ownerDocument;try{if(!(d&&d.nodeName&&c.noData[d.nodeName.toLowerCase()]))if(d[\"on\"+e]&&d[\"on\"+e].apply(d,b)===false)a.result=false}catch(j){}if(!a.isPropagationStopped()&&\
f)c.event.trigger(a,b,f,true);else if(!a.isDefaultPrevented()){f=a.target;var i,o=c.nodeName(f,\"a\")&&e===\"click\",k=c.event.special[e]||{};if((!k._default||k._default.call(d,a)===false)&&!o&&!(f&&f.nodeName&&c.noData[f.nodeName.toLowerCase()])){try{if(f[e]){if(i=f[\"on\"+e])f[\"on\"+e]=null;c.event.triggered=true;f[e]()}}catch(n){}if(i)f[\"on\"+e]=i;c.event.triggered=false}}},handle:function(a){var b,d,f,e;a=arguments[0]=c.event.fix(a||A.event);a.currentTarget=this;b=a.type.indexOf(\".\")<0&&!a.exclusive;\
if(!b){d=a.type.split(\".\");a.type=d.shift();f=new RegExp(\"(^|\\\\.)\"+d.slice(0).sort().join(\"\\\\.(?:.*\\\\.)?\")+\"(\\\\.|$)\")}e=c.data(this,\"events\");d=e[a.type];if(e&&d){d=d.slice(0);e=0;for(var j=d.length;e<j;e++){var i=d[e];if(b||f.test(i.namespace)){a.handler=i.handler;a.data=i.data;a.handleObj=i;i=i.handler.apply(this,arguments);if(i!==w){a.result=i;if(i===false){a.preventDefault();a.stopPropagation()}}if(a.isImmediatePropagationStopped())break}}}return a.result},props:\"altKey attrChange attrName bubbles button cancelable charCode clientX clientY ctrlKey currentTarget data detail eventPhase fromElement handler keyCode layerX layerY metaKey newValue offsetX offsetY originalTarget pageX pageY prevValue relatedNode relatedTarget screenX screenY shiftKey srcElement target toElement view wheelDelta which\".split(\" \"),\
fix:function(a){if(a[G])return a;var b=a;a=c.Event(b);for(var d=this.props.length,f;d;){f=this.props[--d];a[f]=b[f]}if(!a.target)a.target=a.srcElement||s;if(a.target.nodeType===3)a.target=a.target.parentNode;if(!a.relatedTarget&&a.fromElement)a.relatedTarget=a.fromElement===a.target?a.toElement:a.fromElement;if(a.pageX==null&&a.clientX!=null){b=s.documentElement;d=s.body;a.pageX=a.clientX+(b&&b.scrollLeft||d&&d.scrollLeft||0)-(b&&b.clientLeft||d&&d.clientLeft||0);a.pageY=a.clientY+(b&&b.scrollTop||\
d&&d.scrollTop||0)-(b&&b.clientTop||d&&d.clientTop||0)}if(!a.which&&(a.charCode||a.charCode===0?a.charCode:a.keyCode))a.which=a.charCode||a.keyCode;if(!a.metaKey&&a.ctrlKey)a.metaKey=a.ctrlKey;if(!a.which&&a.button!==w)a.which=a.button&1?1:a.button&2?3:a.button&4?2:0;return a},guid:1E8,proxy:c.proxy,special:{ready:{setup:c.bindReady,teardown:c.noop},live:{add:function(a){c.event.add(this,a.origType,c.extend({},a,{handler:oa}))},remove:function(a){var b=true,d=a.origType.replace(O,\"\");c.each(c.data(this,\
\"events\").live||[],function(){if(d===this.origType.replace(O,\"\"))return b=false});b&&c.event.remove(this,a.origType,oa)}},beforeunload:{setup:function(a,b,d){if(this.setInterval)this.onbeforeunload=d;return false},teardown:function(a,b){if(this.onbeforeunload===b)this.onbeforeunload=null}}}};var Ca=s.removeEventListener?function(a,b,d){a.removeEventListener(b,d,false)}:function(a,b,d){a.detachEvent(\"on\"+b,d)};c.Event=function(a){if(!this.preventDefault)return new c.Event(a);if(a&&a.type){this.originalEvent=\
a;this.type=a.type}else this.type=a;this.timeStamp=J();this[G]=true};c.Event.prototype={preventDefault:function(){this.isDefaultPrevented=Z;var a=this.originalEvent;if(a){a.preventDefault&&a.preventDefault();a.returnValue=false}},stopPropagation:function(){this.isPropagationStopped=Z;var a=this.originalEvent;if(a){a.stopPropagation&&a.stopPropagation();a.cancelBubble=true}},stopImmediatePropagation:function(){this.isImmediatePropagationStopped=Z;this.stopPropagation()},isDefaultPrevented:Y,isPropagationStopped:Y,\
isImmediatePropagationStopped:Y};var Da=function(a){var b=a.relatedTarget;try{for(;b&&b!==this;)b=b.parentNode;if(b!==this){a.type=a.data;c.event.handle.apply(this,arguments)}}catch(d){}},Ea=function(a){a.type=a.data;c.event.handle.apply(this,arguments)};c.each({mouseenter:\"mouseover\",mouseleave:\"mouseout\"},function(a,b){c.event.special[a]={setup:function(d){c.event.add(this,b,d&&d.selector?Ea:Da,a)},teardown:function(d){c.event.remove(this,b,d&&d.selector?Ea:Da)}}});if(!c.support.submitBubbles)c.event.special.submit=\
{setup:function(){if(this.nodeName.toLowerCase()!==\"form\"){c.event.add(this,\"click.specialSubmit\",function(a){var b=a.target,d=b.type;if((d===\"submit\"||d===\"image\")&&c(b).closest(\"form\").length)return na(\"submit\",this,arguments)});c.event.add(this,\"keypress.specialSubmit\",function(a){var b=a.target,d=b.type;if((d===\"text\"||d===\"password\")&&c(b).closest(\"form\").length&&a.keyCode===13)return na(\"submit\",this,arguments)})}else return false},teardown:function(){c.event.remove(this,\".specialSubmit\")}};\
if(!c.support.changeBubbles){var da=/textarea|input|select/i,ea,Fa=function(a){var b=a.type,d=a.value;if(b===\"radio\"||b===\"checkbox\")d=a.checked;else if(b===\"select-multiple\")d=a.selectedIndex>-1?c.map(a.options,function(f){return f.selected}).join(\"-\"):\"\";else if(a.nodeName.toLowerCase()===\"select\")d=a.selectedIndex;return d},fa=function(a,b){var d=a.target,f,e;if(!(!da.test(d.nodeName)||d.readOnly)){f=c.data(d,\"_change_data\");e=Fa(d);if(a.type!==\"focusout\"||d.type!==\"radio\")c.data(d,\"_change_data\",\
e);if(!(f===w||e===f))if(f!=null||e){a.type=\"change\";return c.event.trigger(a,b,d)}}};c.event.special.change={filters:{focusout:fa,click:function(a){var b=a.target,d=b.type;if(d===\"radio\"||d===\"checkbox\"||b.nodeName.toLowerCase()===\"select\")return fa.call(this,a)},keydown:function(a){var b=a.target,d=b.type;if(a.keyCode===13&&b.nodeName.toLowerCase()!==\"textarea\"||a.keyCode===32&&(d===\"checkbox\"||d===\"radio\")||d===\"select-multiple\")return fa.call(this,a)},beforeactivate:function(a){a=a.target;c.data(a,\
\"_change_data\",Fa(a))}},setup:function(){if(this.type===\"file\")return false;for(var a in ea)c.event.add(this,a+\".specialChange\",ea[a]);return da.test(this.nodeName)},teardown:function(){c.event.remove(this,\".specialChange\");return da.test(this.nodeName)}};ea=c.event.special.change.filters}s.addEventListener&&c.each({focus:\"focusin\",blur:\"focusout\"},function(a,b){function d(f){f=c.event.fix(f);f.type=b;return c.event.handle.call(this,f)}c.event.special[b]={setup:function(){this.addEventListener(a,\
d,true)},teardown:function(){this.removeEventListener(a,d,true)}}});c.each([\"bind\",\"one\"],function(a,b){c.fn[b]=function(d,f,e){if(typeof d===\"object\"){for(var j in d)this[b](j,f,d[j],e);return this}if(c.isFunction(f)){e=f;f=w}var i=b===\"one\"?c.proxy(e,function(k){c(this).unbind(k,i);return e.apply(this,arguments)}):e;if(d===\"unload\"&&b!==\"one\")this.one(d,f,e);else{j=0;for(var o=this.length;j<o;j++)c.event.add(this[j],d,i,f)}return this}});c.fn.extend({unbind:function(a,b){if(typeof a===\"object\"&&\
!a.preventDefault)for(var d in a)this.unbind(d,a[d]);else{d=0;for(var f=this.length;d<f;d++)c.event.remove(this[d],a,b)}return this},delegate:function(a,b,d,f){return this.live(b,d,f,a)},undelegate:function(a,b,d){return arguments.length===0?this.unbind(\"live\"):this.die(b,null,d,a)},trigger:function(a,b){return this.each(function(){c.event.trigger(a,b,this)})},triggerHandler:function(a,b){if(this[0]){a=c.Event(a);a.preventDefault();a.stopPropagation();c.event.trigger(a,b,this[0]);return a.result}},\
toggle:function(a){for(var b=arguments,d=1;d<b.length;)c.proxy(a,b[d++]);return this.click(c.proxy(a,function(f){var e=(c.data(this,\"lastToggle\"+a.guid)||0)%d;c.data(this,\"lastToggle\"+a.guid,e+1);f.preventDefault();return b[e].apply(this,arguments)||false}))},hover:function(a,b){return this.mouseenter(a).mouseleave(b||a)}});var Ga={focus:\"focusin\",blur:\"focusout\",mouseenter:\"mouseover\",mouseleave:\"mouseout\"};c.each([\"live\",\"die\"],function(a,b){c.fn[b]=function(d,f,e,j){var i,o=0,k,n,r=j||this.selector,\
u=j?this:c(this.context);if(c.isFunction(f)){e=f;f=w}for(d=(d||\"\").split(\" \");(i=d[o++])!=null;){j=O.exec(i);k=\"\";if(j){k=j[0];i=i.replace(O,\"\")}if(i===\"hover\")d.push(\"mouseenter\"+k,\"mouseleave\"+k);else{n=i;if(i===\"focus\"||i===\"blur\"){d.push(Ga[i]+k);i+=k}else i=(Ga[i]||i)+k;b===\"live\"?u.each(function(){c.event.add(this,pa(i,r),{data:f,selector:r,handler:e,origType:i,origHandler:e,preType:n})}):u.unbind(pa(i,r),e)}}return this}});c.each(\"blur focus focusin focusout load resize scroll unload click dblclick mousedown mouseup mousemove mouseover mouseout mouseenter mouseleave change select submit keydown keypress keyup error\".split(\" \"),\
function(a,b){c.fn[b]=function(d){return d?this.bind(b,d):this.trigger(b)};if(c.attrFn)c.attrFn[b]=true});A.attachEvent&&!A.addEventListener&&A.attachEvent(\"onunload\",function(){for(var a in c.cache)if(c.cache[a].handle)try{c.event.remove(c.cache[a].handle.elem)}catch(b){}});(function(){function a(g){for(var h=\"\",l,m=0;g[m];m++){l=g[m];if(l.nodeType===3||l.nodeType===4)h+=l.nodeValue;else if(l.nodeType!==8)h+=a(l.childNodes)}return h}function b(g,h,l,m,q,p){q=0;for(var v=m.length;q<v;q++){var t=m[q];\
if(t){t=t[g];for(var y=false;t;){if(t.sizcache===l){y=m[t.sizset];break}if(t.nodeType===1&&!p){t.sizcache=l;t.sizset=q}if(t.nodeName.toLowerCase()===h){y=t;break}t=t[g]}m[q]=y}}}function d(g,h,l,m,q,p){q=0;for(var v=m.length;q<v;q++){var t=m[q];if(t){t=t[g];for(var y=false;t;){if(t.sizcache===l){y=m[t.sizset];break}if(t.nodeType===1){if(!p){t.sizcache=l;t.sizset=q}if(typeof h!==\"string\"){if(t===h){y=true;break}}else if(k.filter(h,[t]).length>0){y=t;break}}t=t[g]}m[q]=y}}}var f=/((?:\\((?:\\([^()]+\\)|[^()]+)+\\)|\\[(?:\\[[^[\\]]*\\]|['\"][^'\"]*['\"]|[^[\\]'\"]+)+\\]|\\\\.|[^ >+~,(\\[\\\\]+)+|[>+~])(\\s*,\\s*)?((?:.|\\r|\\n)*)/g,\
e=0,j=Object.prototype.toString,i=false,o=true;[0,0].sort(function(){o=false;return 0});var k=function(g,h,l,m){l=l||[];var q=h=h||s;if(h.nodeType!==1&&h.nodeType!==9)return[];if(!g||typeof g!==\"string\")return l;for(var p=[],v,t,y,S,H=true,M=x(h),I=g;(f.exec(\"\"),v=f.exec(I))!==null;){I=v[3];p.push(v[1]);if(v[2]){S=v[3];break}}if(p.length>1&&r.exec(g))if(p.length===2&&n.relative[p[0]])t=ga(p[0]+p[1],h);else for(t=n.relative[p[0]]?[h]:k(p.shift(),h);p.length;){g=p.shift();if(n.relative[g])g+=p.shift();\
t=ga(g,t)}else{if(!m&&p.length>1&&h.nodeType===9&&!M&&n.match.ID.test(p[0])&&!n.match.ID.test(p[p.length-1])){v=k.find(p.shift(),h,M);h=v.expr?k.filter(v.expr,v.set)[0]:v.set[0]}if(h){v=m?{expr:p.pop(),set:z(m)}:k.find(p.pop(),p.length===1&&(p[0]===\"~\"||p[0]===\"+\")&&h.parentNode?h.parentNode:h,M);t=v.expr?k.filter(v.expr,v.set):v.set;if(p.length>0)y=z(t);else H=false;for(;p.length;){var D=p.pop();v=D;if(n.relative[D])v=p.pop();else D=\"\";if(v==null)v=h;n.relative[D](y,v,M)}}else y=[]}y||(y=t);y||k.error(D||\
g);if(j.call(y)===\"[object Array]\")if(H)if(h&&h.nodeType===1)for(g=0;y[g]!=null;g++){if(y[g]&&(y[g]===true||y[g].nodeType===1&&E(h,y[g])))l.push(t[g])}else for(g=0;y[g]!=null;g++)y[g]&&y[g].nodeType===1&&l.push(t[g]);else l.push.apply(l,y);else z(y,l);if(S){k(S,q,l,m);k.uniqueSort(l)}return l};k.uniqueSort=function(g){if(B){i=o;g.sort(B);if(i)for(var h=1;h<g.length;h++)g[h]===g[h-1]&&g.splice(h--,1)}return g};k.matches=function(g,h){return k(g,null,null,h)};k.find=function(g,h,l){var m,q;if(!g)return[];\
for(var p=0,v=n.order.length;p<v;p++){var t=n.order[p];if(q=n.leftMatch[t].exec(g)){var y=q[1];q.splice(1,1);if(y.substr(y.length-1)!==\"\\\\\"){q[1]=(q[1]||\"\").replace(/\\\\/g,\"\");m=n.find[t](q,h,l);if(m!=null){g=g.replace(n.match[t],\"\");break}}}}m||(m=h.getElementsByTagName(\"*\"));return{set:m,expr:g}};k.filter=function(g,h,l,m){for(var q=g,p=[],v=h,t,y,S=h&&h[0]&&x(h[0]);g&&h.length;){for(var H in n.filter)if((t=n.leftMatch[H].exec(g))!=null&&t[2]){var M=n.filter[H],I,D;D=t[1];y=false;t.splice(1,1);if(D.substr(D.length-\
1)!==\"\\\\\"){if(v===p)p=[];if(n.preFilter[H])if(t=n.preFilter[H](t,v,l,p,m,S)){if(t===true)continue}else y=I=true;if(t)for(var U=0;(D=v[U])!=null;U++)if(D){I=M(D,t,U,v);var Ha=m^!!I;if(l&&I!=null)if(Ha)y=true;else v[U]=false;else if(Ha){p.push(D);y=true}}if(I!==w){l||(v=p);g=g.replace(n.match[H],\"\");if(!y)return[];break}}}if(g===q)if(y==null)k.error(g);else break;q=g}return v};k.error=function(g){throw\"Syntax error, unrecognized expression: \"+g;};var n=k.selectors={order:[\"ID\",\"NAME\",\"TAG\"],match:{ID:/#((?:[\\w\\u00c0-\\uFFFF-]|\\\\.)+)/,\
CLASS:/\\.((?:[\\w\\u00c0-\\uFFFF-]|\\\\.)+)/,NAME:/\\[name=['\"]*((?:[\\w\\u00c0-\\uFFFF-]|\\\\.)+)['\"]*\\]/,ATTR:/\\[\\s*((?:[\\w\\u00c0-\\uFFFF-]|\\\\.)+)\\s*(?:(\\S?=)\\s*(['\"]*)(.*?)\\3|)\\s*\\]/,TAG:/^((?:[\\w\\u00c0-\\uFFFF\\*-]|\\\\.)+)/,CHILD:/:(only|nth|last|first)-child(?:\\((even|odd|[\\dn+-]*)\\))?/,POS:/:(nth|eq|gt|lt|first|last|even|odd)(?:\\((\\d*)\\))?(?=[^-]|$)/,PSEUDO:/:((?:[\\w\\u00c0-\\uFFFF-]|\\\\.)+)(?:\\((['\"]?)((?:\\([^\\)]+\\)|[^\\(\\)]*)+)\\2\\))?/},leftMatch:{},attrMap:{\"class\":\"className\",\"for\":\"htmlFor\"},attrHandle:{href:function(g){return g.getAttribute(\"href\")}},\
relative:{\"+\":function(g,h){var l=typeof h===\"string\",m=l&&!/\\W/.test(h);l=l&&!m;if(m)h=h.toLowerCase();m=0;for(var q=g.length,p;m<q;m++)if(p=g[m]){for(;(p=p.previousSibling)&&p.nodeType!==1;);g[m]=l||p&&p.nodeName.toLowerCase()===h?p||false:p===h}l&&k.filter(h,g,true)},\">\":function(g,h){var l=typeof h===\"string\";if(l&&!/\\W/.test(h)){h=h.toLowerCase();for(var m=0,q=g.length;m<q;m++){var p=g[m];if(p){l=p.parentNode;g[m]=l.nodeName.toLowerCase()===h?l:false}}}else{m=0;for(q=g.length;m<q;m++)if(p=g[m])g[m]=\
l?p.parentNode:p.parentNode===h;l&&k.filter(h,g,true)}},\"\":function(g,h,l){var m=e++,q=d;if(typeof h===\"string\"&&!/\\W/.test(h)){var p=h=h.toLowerCase();q=b}q(\"parentNode\",h,m,g,p,l)},\"~\":function(g,h,l){var m=e++,q=d;if(typeof h===\"string\"&&!/\\W/.test(h)){var p=h=h.toLowerCase();q=b}q(\"previousSibling\",h,m,g,p,l)}},find:{ID:function(g,h,l){if(typeof h.getElementById!==\"undefined\"&&!l)return(g=h.getElementById(g[1]))?[g]:[]},NAME:function(g,h){if(typeof h.getElementsByName!==\"undefined\"){var l=[];\
h=h.getElementsByName(g[1]);for(var m=0,q=h.length;m<q;m++)h[m].getAttribute(\"name\")===g[1]&&l.push(h[m]);return l.length===0?null:l}},TAG:function(g,h){return h.getElementsByTagName(g[1])}},preFilter:{CLASS:function(g,h,l,m,q,p){g=\" \"+g[1].replace(/\\\\/g,\"\")+\" \";if(p)return g;p=0;for(var v;(v=h[p])!=null;p++)if(v)if(q^(v.className&&(\" \"+v.className+\" \").replace(/[\\t\\n]/g,\" \").indexOf(g)>=0))l||m.push(v);else if(l)h[p]=false;return false},ID:function(g){return g[1].replace(/\\\\/g,\"\")},TAG:function(g){return g[1].toLowerCase()},\
CHILD:function(g){if(g[1]===\"nth\"){var h=/(-?)(\\d*)n((?:\\+|-)?\\d*)/.exec(g[2]===\"even\"&&\"2n\"||g[2]===\"odd\"&&\"2n+1\"||!/\\D/.test(g[2])&&\"0n+\"+g[2]||g[2]);g[2]=h[1]+(h[2]||1)-0;g[3]=h[3]-0}g[0]=e++;return g},ATTR:function(g,h,l,m,q,p){h=g[1].replace(/\\\\/g,\"\");if(!p&&n.attrMap[h])g[1]=n.attrMap[h];if(g[2]===\"~=\")g[4]=\" \"+g[4]+\" \";return g},PSEUDO:function(g,h,l,m,q){if(g[1]===\"not\")if((f.exec(g[3])||\"\").length>1||/^\\w/.test(g[3]))g[3]=k(g[3],null,null,h);else{g=k.filter(g[3],h,l,true^q);l||m.push.apply(m,\
g);return false}else if(n.match.POS.test(g[0])||n.match.CHILD.test(g[0]))return true;return g},POS:function(g){g.unshift(true);return g}},filters:{enabled:function(g){return g.disabled===false&&g.type!==\"hidden\"},disabled:function(g){return g.disabled===true},checked:function(g){return g.checked===true},selected:function(g){return g.selected===true},parent:function(g){return!!g.firstChild},empty:function(g){return!g.firstChild},has:function(g,h,l){return!!k(l[3],g).length},header:function(g){return/h\\d/i.test(g.nodeName)},\
text:function(g){return\"text\"===g.type},radio:function(g){return\"radio\"===g.type},checkbox:function(g){return\"checkbox\"===g.type},file:function(g){return\"file\"===g.type},password:function(g){return\"password\"===g.type},submit:function(g){return\"submit\"===g.type},image:function(g){return\"image\"===g.type},reset:function(g){return\"reset\"===g.type},button:function(g){return\"button\"===g.type||g.nodeName.toLowerCase()===\"button\"},input:function(g){return/input|select|textarea|button/i.test(g.nodeName)}},\
setFilters:{first:function(g,h){return h===0},last:function(g,h,l,m){return h===m.length-1},even:function(g,h){return h%2===0},odd:function(g,h){return h%2===1},lt:function(g,h,l){return h<l[3]-0},gt:function(g,h,l){return h>l[3]-0},nth:function(g,h,l){return l[3]-0===h},eq:function(g,h,l){return l[3]-0===h}},filter:{PSEUDO:function(g,h,l,m){var q=h[1],p=n.filters[q];if(p)return p(g,l,h,m);else if(q===\"contains\")return(g.textContent||g.innerText||a([g])||\"\").indexOf(h[3])>=0;else if(q===\"not\"){h=\
h[3];l=0;for(m=h.length;l<m;l++)if(h[l]===g)return false;return true}else k.error(\"Syntax error, unrecognized expression: \"+q)},CHILD:function(g,h){var l=h[1],m=g;switch(l){case \"only\":case \"first\":for(;m=m.previousSibling;)if(m.nodeType===1)return false;if(l===\"first\")return true;m=g;case \"last\":for(;m=m.nextSibling;)if(m.nodeType===1)return false;return true;case \"nth\":l=h[2];var q=h[3];if(l===1&&q===0)return true;h=h[0];var p=g.parentNode;if(p&&(p.sizcache!==h||!g.nodeIndex)){var v=0;for(m=p.firstChild;m;m=\
m.nextSibling)if(m.nodeType===1)m.nodeIndex=++v;p.sizcache=h}g=g.nodeIndex-q;return l===0?g===0:g%l===0&&g/l>=0}},ID:function(g,h){return g.nodeType===1&&g.getAttribute(\"id\")===h},TAG:function(g,h){return h===\"*\"&&g.nodeType===1||g.nodeName.toLowerCase()===h},CLASS:function(g,h){return(\" \"+(g.className||g.getAttribute(\"class\"))+\" \").indexOf(h)>-1},ATTR:function(g,h){var l=h[1];g=n.attrHandle[l]?n.attrHandle[l](g):g[l]!=null?g[l]:g.getAttribute(l);l=g+\"\";var m=h[2];h=h[4];return g==null?m===\"!=\":m===\
\"=\"?l===h:m===\"*=\"?l.indexOf(h)>=0:m===\"~=\"?(\" \"+l+\" \").indexOf(h)>=0:!h?l&&g!==false:m===\"!=\"?l!==h:m===\"^=\"?l.indexOf(h)===0:m===\"$=\"?l.substr(l.length-h.length)===h:m===\"|=\"?l===h||l.substr(0,h.length+1)===h+\"-\":false},POS:function(g,h,l,m){var q=n.setFilters[h[2]];if(q)return q(g,l,h,m)}}},r=n.match.POS;for(var u in n.match){n.match[u]=new RegExp(n.match[u].source+/(?![^\\[]*\\])(?![^\\(]*\\))/.source);n.leftMatch[u]=new RegExp(/(^(?:.|\\r|\\n)*?)/.source+n.match[u].source.replace(/\\\\(\\d+)/g,function(g,\
h){return\"\\\\\"+(h-0+1)}))}var z=function(g,h){g=Array.prototype.slice.call(g,0);if(h){h.push.apply(h,g);return h}return g};try{Array.prototype.slice.call(s.documentElement.childNodes,0)}catch(C){z=function(g,h){h=h||[];if(j.call(g)===\"[object Array]\")Array.prototype.push.apply(h,g);else if(typeof g.length===\"number\")for(var l=0,m=g.length;l<m;l++)h.push(g[l]);else for(l=0;g[l];l++)h.push(g[l]);return h}}var B;if(s.documentElement.compareDocumentPosition)B=function(g,h){if(!g.compareDocumentPosition||\
!h.compareDocumentPosition){if(g==h)i=true;return g.compareDocumentPosition?-1:1}g=g.compareDocumentPosition(h)&4?-1:g===h?0:1;if(g===0)i=true;return g};else if(\"sourceIndex\"in s.documentElement)B=function(g,h){if(!g.sourceIndex||!h.sourceIndex){if(g==h)i=true;return g.sourceIndex?-1:1}g=g.sourceIndex-h.sourceIndex;if(g===0)i=true;return g};else if(s.createRange)B=function(g,h){if(!g.ownerDocument||!h.ownerDocument){if(g==h)i=true;return g.ownerDocument?-1:1}var l=g.ownerDocument.createRange(),m=\
h.ownerDocument.createRange();l.setStart(g,0);l.setEnd(g,0);m.setStart(h,0);m.setEnd(h,0);g=l.compareBoundaryPoints(Range.START_TO_END,m);if(g===0)i=true;return g};(function(){var g=s.createElement(\"div\"),h=\"script\"+(new Date).getTime();g.innerHTML=\"<a name='\"+h+\"'/>\";var l=s.documentElement;l.insertBefore(g,l.firstChild);if(s.getElementById(h)){n.find.ID=function(m,q,p){if(typeof q.getElementById!==\"undefined\"&&!p)return(q=q.getElementById(m[1]))?q.id===m[1]||typeof q.getAttributeNode!==\"undefined\"&&\
q.getAttributeNode(\"id\").nodeValue===m[1]?[q]:w:[]};n.filter.ID=function(m,q){var p=typeof m.getAttributeNode!==\"undefined\"&&m.getAttributeNode(\"id\");return m.nodeType===1&&p&&p.nodeValue===q}}l.removeChild(g);l=g=null})();(function(){var g=s.createElement(\"div\");g.appendChild(s.createComment(\"\"));if(g.getElementsByTagName(\"*\").length>0)n.find.TAG=function(h,l){l=l.getElementsByTagName(h[1]);if(h[1]===\"*\"){h=[];for(var m=0;l[m];m++)l[m].nodeType===1&&h.push(l[m]);l=h}return l};g.innerHTML=\"<a href='#'></a>\";\
if(g.firstChild&&typeof g.firstChild.getAttribute!==\"undefined\"&&g.firstChild.getAttribute(\"href\")!==\"#\")n.attrHandle.href=function(h){return h.getAttribute(\"href\",2)};g=null})();s.querySelectorAll&&function(){var g=k,h=s.createElement(\"div\");h.innerHTML=\"<p class='TEST'></p>\";if(!(h.querySelectorAll&&h.querySelectorAll(\".TEST\").length===0)){k=function(m,q,p,v){q=q||s;if(!v&&q.nodeType===9&&!x(q))try{return z(q.querySelectorAll(m),p)}catch(t){}return g(m,q,p,v)};for(var l in g)k[l]=g[l];h=null}}();\
(function(){var g=s.createElement(\"div\");g.innerHTML=\"<div class='test e'></div><div class='test'></div>\";if(!(!g.getElementsByClassName||g.getElementsByClassName(\"e\").length===0)){g.lastChild.className=\"e\";if(g.getElementsByClassName(\"e\").length!==1){n.order.splice(1,0,\"CLASS\");n.find.CLASS=function(h,l,m){if(typeof l.getElementsByClassName!==\"undefined\"&&!m)return l.getElementsByClassName(h[1])};g=null}}})();var E=s.compareDocumentPosition?function(g,h){return!!(g.compareDocumentPosition(h)&16)}:\
function(g,h){return g!==h&&(g.contains?g.contains(h):true)},x=function(g){return(g=(g?g.ownerDocument||g:0).documentElement)?g.nodeName!==\"HTML\":false},ga=function(g,h){var l=[],m=\"\",q;for(h=h.nodeType?[h]:h;q=n.match.PSEUDO.exec(g);){m+=q[0];g=g.replace(n.match.PSEUDO,\"\")}g=n.relative[g]?g+\"*\":g;q=0;for(var p=h.length;q<p;q++)k(g,h[q],l);return k.filter(m,l)};c.find=k;c.expr=k.selectors;c.expr[\":\"]=c.expr.filters;c.unique=k.uniqueSort;c.text=a;c.isXMLDoc=x;c.contains=E})();var eb=/Until$/,fb=/^(?:parents|prevUntil|prevAll)/,\
gb=/,/;R=Array.prototype.slice;var Ia=function(a,b,d){if(c.isFunction(b))return c.grep(a,function(e,j){return!!b.call(e,j,e)===d});else if(b.nodeType)return c.grep(a,function(e){return e===b===d});else if(typeof b===\"string\"){var f=c.grep(a,function(e){return e.nodeType===1});if(Ua.test(b))return c.filter(b,f,!d);else b=c.filter(b,f)}return c.grep(a,function(e){return c.inArray(e,b)>=0===d})};c.fn.extend({find:function(a){for(var b=this.pushStack(\"\",\"find\",a),d=0,f=0,e=this.length;f<e;f++){d=b.length;\
c.find(a,this[f],b);if(f>0)for(var j=d;j<b.length;j++)for(var i=0;i<d;i++)if(b[i]===b[j]){b.splice(j--,1);break}}return b},has:function(a){var b=c(a);return this.filter(function(){for(var d=0,f=b.length;d<f;d++)if(c.contains(this,b[d]))return true})},not:function(a){return this.pushStack(Ia(this,a,false),\"not\",a)},filter:function(a){return this.pushStack(Ia(this,a,true),\"filter\",a)},is:function(a){return!!a&&c.filter(a,this).length>0},closest:function(a,b){if(c.isArray(a)){var d=[],f=this[0],e,j=\
{},i;if(f&&a.length){e=0;for(var o=a.length;e<o;e++){i=a[e];j[i]||(j[i]=c.expr.match.POS.test(i)?c(i,b||this.context):i)}for(;f&&f.ownerDocument&&f!==b;){for(i in j){e=j[i];if(e.jquery?e.index(f)>-1:c(f).is(e)){d.push({selector:i,elem:f});delete j[i]}}f=f.parentNode}}return d}var k=c.expr.match.POS.test(a)?c(a,b||this.context):null;return this.map(function(n,r){for(;r&&r.ownerDocument&&r!==b;){if(k?k.index(r)>-1:c(r).is(a))return r;r=r.parentNode}return null})},index:function(a){if(!a||typeof a===\
\"string\")return c.inArray(this[0],a?c(a):this.parent().children());return c.inArray(a.jquery?a[0]:a,this)},add:function(a,b){a=typeof a===\"string\"?c(a,b||this.context):c.makeArray(a);b=c.merge(this.get(),a);return this.pushStack(qa(a[0])||qa(b[0])?b:c.unique(b))},andSelf:function(){return this.add(this.prevObject)}});c.each({parent:function(a){return(a=a.parentNode)&&a.nodeType!==11?a:null},parents:function(a){return c.dir(a,\"parentNode\")},parentsUntil:function(a,b,d){return c.dir(a,\"parentNode\",\
d)},next:function(a){return c.nth(a,2,\"nextSibling\")},prev:function(a){return c.nth(a,2,\"previousSibling\")},nextAll:function(a){return c.dir(a,\"nextSibling\")},prevAll:function(a){return c.dir(a,\"previousSibling\")},nextUntil:function(a,b,d){return c.dir(a,\"nextSibling\",d)},prevUntil:function(a,b,d){return c.dir(a,\"previousSibling\",d)},siblings:function(a){return c.sibling(a.parentNode.firstChild,a)},children:function(a){return c.sibling(a.firstChild)},contents:function(a){return c.nodeName(a,\"iframe\")?\
a.contentDocument||a.contentWindow.document:c.makeArray(a.childNodes)}},function(a,b){c.fn[a]=function(d,f){var e=c.map(this,b,d);eb.test(a)||(f=d);if(f&&typeof f===\"string\")e=c.filter(f,e);e=this.length>1?c.unique(e):e;if((this.length>1||gb.test(f))&&fb.test(a))e=e.reverse();return this.pushStack(e,a,R.call(arguments).join(\",\"))}});c.extend({filter:function(a,b,d){if(d)a=\":not(\"+a+\")\";return c.find.matches(a,b)},dir:function(a,b,d){var f=[];for(a=a[b];a&&a.nodeType!==9&&(d===w||a.nodeType!==1||!c(a).is(d));){a.nodeType===\
1&&f.push(a);a=a[b]}return f},nth:function(a,b,d){b=b||1;for(var f=0;a;a=a[d])if(a.nodeType===1&&++f===b)break;return a},sibling:function(a,b){for(var d=[];a;a=a.nextSibling)a.nodeType===1&&a!==b&&d.push(a);return d}});var Ja=/ jQuery\\d+=\"(?:\\d+|null)\"/g,V=/^\\s+/,Ka=/(<([\\w:]+)[^>]*?)\\/>/g,hb=/^(?:area|br|col|embed|hr|img|input|link|meta|param)$/i,La=/<([\\w:]+)/,ib=/<tbody/i,jb=/<|&#?\\w+;/,ta=/<script|<object|<embed|<option|<style/i,ua=/checked\\s*(?:[^=]|=\\s*.checked.)/i,Ma=function(a,b,d){return hb.test(d)?\
a:b+\"></\"+d+\">\"},F={option:[1,\"<select multiple='multiple'>\",\"</select>\"],legend:[1,\"<fieldset>\",\"</fieldset>\"],thead:[1,\"<table>\",\"</table>\"],tr:[2,\"<table><tbody>\",\"</tbody></table>\"],td:[3,\"<table><tbody><tr>\",\"</tr></tbody></table>\"],col:[2,\"<table><tbody></tbody><colgroup>\",\"</colgroup></table>\"],area:[1,\"<map>\",\"</map>\"],_default:[0,\"\",\"\"]};F.optgroup=F.option;F.tbody=F.tfoot=F.colgroup=F.caption=F.thead;F.th=F.td;if(!c.support.htmlSerialize)F._default=[1,\"div<div>\",\"</div>\"];c.fn.extend({text:function(a){if(c.isFunction(a))return this.each(function(b){var d=\
c(this);d.text(a.call(this,b,d.text()))});if(typeof a!==\"object\"&&a!==w)return this.empty().append((this[0]&&this[0].ownerDocument||s).createTextNode(a));return c.text(this)},wrapAll:function(a){if(c.isFunction(a))return this.each(function(d){c(this).wrapAll(a.call(this,d))});if(this[0]){var b=c(a,this[0].ownerDocument).eq(0).clone(true);this[0].parentNode&&b.insertBefore(this[0]);b.map(function(){for(var d=this;d.firstChild&&d.firstChild.nodeType===1;)d=d.firstChild;return d}).append(this)}return this},\
wrapInner:function(a){if(c.isFunction(a))return this.each(function(b){c(this).wrapInner(a.call(this,b))});return this.each(function(){var b=c(this),d=b.contents();d.length?d.wrapAll(a):b.append(a)})},wrap:function(a){return this.each(function(){c(this).wrapAll(a)})},unwrap:function(){return this.parent().each(function(){c.nodeName(this,\"body\")||c(this).replaceWith(this.childNodes)}).end()},append:function(){return this.domManip(arguments,true,function(a){this.nodeType===1&&this.appendChild(a)})},\
prepend:function(){return this.domManip(arguments,true,function(a){this.nodeType===1&&this.insertBefore(a,this.firstChild)})},before:function(){if(this[0]&&this[0].parentNode)return this.domManip(arguments,false,function(b){this.parentNode.insertBefore(b,this)});else if(arguments.length){var a=c(arguments[0]);a.push.apply(a,this.toArray());return this.pushStack(a,\"before\",arguments)}},after:function(){if(this[0]&&this[0].parentNode)return this.domManip(arguments,false,function(b){this.parentNode.insertBefore(b,\
this.nextSibling)});else if(arguments.length){var a=this.pushStack(this,\"after\",arguments);a.push.apply(a,c(arguments[0]).toArray());return a}},remove:function(a,b){for(var d=0,f;(f=this[d])!=null;d++)if(!a||c.filter(a,[f]).length){if(!b&&f.nodeType===1){c.cleanData(f.getElementsByTagName(\"*\"));c.cleanData([f])}f.parentNode&&f.parentNode.removeChild(f)}return this},empty:function(){for(var a=0,b;(b=this[a])!=null;a++)for(b.nodeType===1&&c.cleanData(b.getElementsByTagName(\"*\"));b.firstChild;)b.removeChild(b.firstChild);\
return this},clone:function(a){var b=this.map(function(){if(!c.support.noCloneEvent&&!c.isXMLDoc(this)){var d=this.outerHTML,f=this.ownerDocument;if(!d){d=f.createElement(\"div\");d.appendChild(this.cloneNode(true));d=d.innerHTML}return c.clean([d.replace(Ja,\"\").replace(/=([^=\"'>\\s]+\\/)>/g,'=\"$1\">').replace(V,\"\")],f)[0]}else return this.cloneNode(true)});if(a===true){ra(this,b);ra(this.find(\"*\"),b.find(\"*\"))}return b},html:function(a){if(a===w)return this[0]&&this[0].nodeType===1?this[0].innerHTML.replace(Ja,\
\"\"):null;else if(typeof a===\"string\"&&!ta.test(a)&&(c.support.leadingWhitespace||!V.test(a))&&!F[(La.exec(a)||[\"\",\"\"])[1].toLowerCase()]){a=a.replace(Ka,Ma);try{for(var b=0,d=this.length;b<d;b++)if(this[b].nodeType===1){c.cleanData(this[b].getElementsByTagName(\"*\"));this[b].innerHTML=a}}catch(f){this.empty().append(a)}}else c.isFunction(a)?this.each(function(e){var j=c(this),i=j.html();j.empty().append(function(){return a.call(this,e,i)})}):this.empty().append(a);return this},replaceWith:function(a){if(this[0]&&\
this[0].parentNode){if(c.isFunction(a))return this.each(function(b){var d=c(this),f=d.html();d.replaceWith(a.call(this,b,f))});if(typeof a!==\"string\")a=c(a).detach();return this.each(function(){var b=this.nextSibling,d=this.parentNode;c(this).remove();b?c(b).before(a):c(d).append(a)})}else return this.pushStack(c(c.isFunction(a)?a():a),\"replaceWith\",a)},detach:function(a){return this.remove(a,true)},domManip:function(a,b,d){function f(u){return c.nodeName(u,\"table\")?u.getElementsByTagName(\"tbody\")[0]||\
u.appendChild(u.ownerDocument.createElement(\"tbody\")):u}var e,j,i=a[0],o=[],k;if(!c.support.checkClone&&arguments.length===3&&typeof i===\"string\"&&ua.test(i))return this.each(function(){c(this).domManip(a,b,d,true)});if(c.isFunction(i))return this.each(function(u){var z=c(this);a[0]=i.call(this,u,b?z.html():w);z.domManip(a,b,d)});if(this[0]){e=i&&i.parentNode;e=c.support.parentNode&&e&&e.nodeType===11&&e.childNodes.length===this.length?{fragment:e}:sa(a,this,o);k=e.fragment;if(j=k.childNodes.length===\
1?(k=k.firstChild):k.firstChild){b=b&&c.nodeName(j,\"tr\");for(var n=0,r=this.length;n<r;n++)d.call(b?f(this[n],j):this[n],n>0||e.cacheable||this.length>1?k.cloneNode(true):k)}o.length&&c.each(o,Qa)}return this}});c.fragments={};c.each({appendTo:\"append\",prependTo:\"prepend\",insertBefore:\"before\",insertAfter:\"after\",replaceAll:\"replaceWith\"},function(a,b){c.fn[a]=function(d){var f=[];d=c(d);var e=this.length===1&&this[0].parentNode;if(e&&e.nodeType===11&&e.childNodes.length===1&&d.length===1){d[b](this[0]);\
return this}else{e=0;for(var j=d.length;e<j;e++){var i=(e>0?this.clone(true):this).get();c.fn[b].apply(c(d[e]),i);f=f.concat(i)}return this.pushStack(f,a,d.selector)}}});c.extend({clean:function(a,b,d,f){b=b||s;if(typeof b.createElement===\"undefined\")b=b.ownerDocument||b[0]&&b[0].ownerDocument||s;for(var e=[],j=0,i;(i=a[j])!=null;j++){if(typeof i===\"number\")i+=\"\";if(i){if(typeof i===\"string\"&&!jb.test(i))i=b.createTextNode(i);else if(typeof i===\"string\"){i=i.replace(Ka,Ma);var o=(La.exec(i)||[\"\",\
\"\"])[1].toLowerCase(),k=F[o]||F._default,n=k[0],r=b.createElement(\"div\");for(r.innerHTML=k[1]+i+k[2];n--;)r=r.lastChild;if(!c.support.tbody){n=ib.test(i);o=o===\"table\"&&!n?r.firstChild&&r.firstChild.childNodes:k[1]===\"<table>\"&&!n?r.childNodes:[];for(k=o.length-1;k>=0;--k)c.nodeName(o[k],\"tbody\")&&!o[k].childNodes.length&&o[k].parentNode.removeChild(o[k])}!c.support.leadingWhitespace&&V.test(i)&&r.insertBefore(b.createTextNode(V.exec(i)[0]),r.firstChild);i=r.childNodes}if(i.nodeType)e.push(i);else e=\
c.merge(e,i)}}if(d)for(j=0;e[j];j++)if(f&&c.nodeName(e[j],\"script\")&&(!e[j].type||e[j].type.toLowerCase()===\"text/javascript\"))f.push(e[j].parentNode?e[j].parentNode.removeChild(e[j]):e[j]);else{e[j].nodeType===1&&e.splice.apply(e,[j+1,0].concat(c.makeArray(e[j].getElementsByTagName(\"script\"))));d.appendChild(e[j])}return e},cleanData:function(a){for(var b,d,f=c.cache,e=c.event.special,j=c.support.deleteExpando,i=0,o;(o=a[i])!=null;i++)if(d=o[c.expando]){b=f[d];if(b.events)for(var k in b.events)e[k]?\
c.event.remove(o,k):Ca(o,k,b.handle);if(j)delete o[c.expando];else o.removeAttribute&&o.removeAttribute(c.expando);delete f[d]}}});var kb=/z-?index|font-?weight|opacity|zoom|line-?height/i,Na=/alpha\\([^)]*\\)/,Oa=/opacity=([^)]*)/,ha=/float/i,ia=/-([a-z])/ig,lb=/([A-Z])/g,mb=/^-?\\d+(?:px)?$/i,nb=/^-?\\d/,ob={position:\"absolute\",visibility:\"hidden\",display:\"block\"},pb=[\"Left\",\"Right\"],qb=[\"Top\",\"Bottom\"],rb=s.defaultView&&s.defaultView.getComputedStyle,Pa=c.support.cssFloat?\"cssFloat\":\"styleFloat\",ja=\
function(a,b){return b.toUpperCase()};c.fn.css=function(a,b){return X(this,a,b,true,function(d,f,e){if(e===w)return c.curCSS(d,f);if(typeof e===\"number\"&&!kb.test(f))e+=\"px\";c.style(d,f,e)})};c.extend({style:function(a,b,d){if(!a||a.nodeType===3||a.nodeType===8)return w;if((b===\"width\"||b===\"height\")&&parseFloat(d)<0)d=w;var f=a.style||a,e=d!==w;if(!c.support.opacity&&b===\"opacity\"){if(e){f.zoom=1;b=parseInt(d,10)+\"\"===\"NaN\"?\"\":\"alpha(opacity=\"+d*100+\")\";a=f.filter||c.curCSS(a,\"filter\")||\"\";f.filter=\
Na.test(a)?a.replace(Na,b):b}return f.filter&&f.filter.indexOf(\"opacity=\")>=0?parseFloat(Oa.exec(f.filter)[1])/100+\"\":\"\"}if(ha.test(b))b=Pa;b=b.replace(ia,ja);if(e)f[b]=d;return f[b]},css:function(a,b,d,f){if(b===\"width\"||b===\"height\"){var e,j=b===\"width\"?pb:qb;function i(){e=b===\"width\"?a.offsetWidth:a.offsetHeight;f!==\"border\"&&c.each(j,function(){f||(e-=parseFloat(c.curCSS(a,\"padding\"+this,true))||0);if(f===\"margin\")e+=parseFloat(c.curCSS(a,\"margin\"+this,true))||0;else e-=parseFloat(c.curCSS(a,\
\"border\"+this+\"Width\",true))||0})}a.offsetWidth!==0?i():c.swap(a,ob,i);return Math.max(0,Math.round(e))}return c.curCSS(a,b,d)},curCSS:function(a,b,d){var f,e=a.style;if(!c.support.opacity&&b===\"opacity\"&&a.currentStyle){f=Oa.test(a.currentStyle.filter||\"\")?parseFloat(RegExp.$1)/100+\"\":\"\";return f===\"\"?\"1\":f}if(ha.test(b))b=Pa;if(!d&&e&&e[b])f=e[b];else if(rb){if(ha.test(b))b=\"float\";b=b.replace(lb,\"-$1\").toLowerCase();e=a.ownerDocument.defaultView;if(!e)return null;if(a=e.getComputedStyle(a,null))f=\
a.getPropertyValue(b);if(b===\"opacity\"&&f===\"\")f=\"1\"}else if(a.currentStyle){d=b.replace(ia,ja);f=a.currentStyle[b]||a.currentStyle[d];if(!mb.test(f)&&nb.test(f)){b=e.left;var j=a.runtimeStyle.left;a.runtimeStyle.left=a.currentStyle.left;e.left=d===\"fontSize\"?\"1em\":f||0;f=e.pixelLeft+\"px\";e.left=b;a.runtimeStyle.left=j}}return f},swap:function(a,b,d){var f={};for(var e in b){f[e]=a.style[e];a.style[e]=b[e]}d.call(a);for(e in b)a.style[e]=f[e]}});if(c.expr&&c.expr.filters){c.expr.filters.hidden=function(a){var b=\
a.offsetWidth,d=a.offsetHeight,f=a.nodeName.toLowerCase()===\"tr\";return b===0&&d===0&&!f?true:b>0&&d>0&&!f?false:c.curCSS(a,\"display\")===\"none\"};c.expr.filters.visible=function(a){return!c.expr.filters.hidden(a)}}var sb=J(),tb=/<script(.|\\s)*?\\/script>/gi,ub=/select|textarea/i,vb=/color|date|datetime|email|hidden|month|number|password|range|search|tel|text|time|url|week/i,N=/=\\?(&|$)/,ka=/\\?/,wb=/(\\?|&)_=.*?(&|$)/,xb=/^(\\w+:)?\\/\\/([^\\/?#]+)/,yb=/%20/g,zb=c.fn.load;c.fn.extend({load:function(a,b,d){if(typeof a!==\
\"string\")return zb.call(this,a);else if(!this.length)return this;var f=a.indexOf(\" \");if(f>=0){var e=a.slice(f,a.length);a=a.slice(0,f)}f=\"GET\";if(b)if(c.isFunction(b)){d=b;b=null}else if(typeof b===\"object\"){b=c.param(b,c.ajaxSettings.traditional);f=\"POST\"}var j=this;c.ajax({url:a,type:f,dataType:\"html\",data:b,complete:function(i,o){if(o===\"success\"||o===\"notmodified\")j.html(e?c(\"<div />\").append(i.responseText.replace(tb,\"\")).find(e):i.responseText);d&&j.each(d,[i.responseText,o,i])}});return this},\
serialize:function(){return c.param(this.serializeArray())},serializeArray:function(){return this.map(function(){return this.elements?c.makeArray(this.elements):this}).filter(function(){return this.name&&!this.disabled&&(this.checked||ub.test(this.nodeName)||vb.test(this.type))}).map(function(a,b){a=c(this).val();return a==null?null:c.isArray(a)?c.map(a,function(d){return{name:b.name,value:d}}):{name:b.name,value:a}}).get()}});c.each(\"ajaxStart ajaxStop ajaxComplete ajaxError ajaxSuccess ajaxSend\".split(\" \"),\
function(a,b){c.fn[b]=function(d){return this.bind(b,d)}});c.extend({get:function(a,b,d,f){if(c.isFunction(b)){f=f||d;d=b;b=null}return c.ajax({type:\"GET\",url:a,data:b,success:d,dataType:f})},getScript:function(a,b){return c.get(a,null,b,\"script\")},getJSON:function(a,b,d){return c.get(a,b,d,\"json\")},post:function(a,b,d,f){if(c.isFunction(b)){f=f||d;d=b;b={}}return c.ajax({type:\"POST\",url:a,data:b,success:d,dataType:f})},ajaxSetup:function(a){c.extend(c.ajaxSettings,a)},ajaxSettings:{url:location.href,\
global:true,type:\"GET\",contentType:\"application/x-www-form-urlencoded\",processData:true,async:true,xhr:A.XMLHttpRequest&&(A.location.protocol!==\"file:\"||!A.ActiveXObject)?function(){return new A.XMLHttpRequest}:function(){try{return new A.ActiveXObject(\"Microsoft.XMLHTTP\")}catch(a){}},accepts:{xml:\"application/xml, text/xml\",html:\"text/html\",script:\"text/javascript, application/javascript\",json:\"application/json, text/javascript\",text:\"text/plain\",_default:\"*/*\"}},lastModified:{},etag:{},ajax:function(a){function b(){e.success&&\
e.success.call(k,o,i,x);e.global&&f(\"ajaxSuccess\",[x,e])}function d(){e.complete&&e.complete.call(k,x,i);e.global&&f(\"ajaxComplete\",[x,e]);e.global&&!--c.active&&c.event.trigger(\"ajaxStop\")}function f(q,p){(e.context?c(e.context):c.event).trigger(q,p)}var e=c.extend(true,{},c.ajaxSettings,a),j,i,o,k=a&&a.context||e,n=e.type.toUpperCase();if(e.data&&e.processData&&typeof e.data!==\"string\")e.data=c.param(e.data,e.traditional);if(e.dataType===\"jsonp\"){if(n===\"GET\")N.test(e.url)||(e.url+=(ka.test(e.url)?\
\"&\":\"?\")+(e.jsonp||\"callback\")+\"=?\");else if(!e.data||!N.test(e.data))e.data=(e.data?e.data+\"&\":\"\")+(e.jsonp||\"callback\")+\"=?\";e.dataType=\"json\"}if(e.dataType===\"json\"&&(e.data&&N.test(e.data)||N.test(e.url))){j=e.jsonpCallback||\"jsonp\"+sb++;if(e.data)e.data=(e.data+\"\").replace(N,\"=\"+j+\"$1\");e.url=e.url.replace(N,\"=\"+j+\"$1\");e.dataType=\"script\";A[j]=A[j]||function(q){o=q;b();d();A[j]=w;try{delete A[j]}catch(p){}z&&z.removeChild(C)}}if(e.dataType===\"script\"&&e.cache===null)e.cache=false;if(e.cache===\
false&&n===\"GET\"){var r=J(),u=e.url.replace(wb,\"$1_=\"+r+\"$2\");e.url=u+(u===e.url?(ka.test(e.url)?\"&\":\"?\")+\"_=\"+r:\"\")}if(e.data&&n===\"GET\")e.url+=(ka.test(e.url)?\"&\":\"?\")+e.data;e.global&&!c.active++&&c.event.trigger(\"ajaxStart\");r=(r=xb.exec(e.url))&&(r[1]&&r[1]!==location.protocol||r[2]!==location.host);if(e.dataType===\"script\"&&n===\"GET\"&&r){var z=s.getElementsByTagName(\"head\")[0]||s.documentElement,C=s.createElement(\"script\");C.src=e.url;if(e.scriptCharset)C.charset=e.scriptCharset;if(!j){var B=\
false;C.onload=C.onreadystatechange=function(){if(!B&&(!this.readyState||this.readyState===\"loaded\"||this.readyState===\"complete\")){B=true;b();d();C.onload=C.onreadystatechange=null;z&&C.parentNode&&z.removeChild(C)}}}z.insertBefore(C,z.firstChild);return w}var E=false,x=e.xhr();if(x){e.username?x.open(n,e.url,e.async,e.username,e.password):x.open(n,e.url,e.async);try{if(e.data||a&&a.contentType)x.setRequestHeader(\"Content-Type\",e.contentType);if(e.ifModified){c.lastModified[e.url]&&x.setRequestHeader(\"If-Modified-Since\",\
c.lastModified[e.url]);c.etag[e.url]&&x.setRequestHeader(\"If-None-Match\",c.etag[e.url])}r||x.setRequestHeader(\"X-Requested-With\",\"XMLHttpRequest\");x.setRequestHeader(\"Accept\",e.dataType&&e.accepts[e.dataType]?e.accepts[e.dataType]+\", */*\":e.accepts._default)}catch(ga){}if(e.beforeSend&&e.beforeSend.call(k,x,e)===false){e.global&&!--c.active&&c.event.trigger(\"ajaxStop\");x.abort();return false}e.global&&f(\"ajaxSend\",[x,e]);var g=x.onreadystatechange=function(q){if(!x||x.readyState===0||q===\"abort\"){E||\
d();E=true;if(x)x.onreadystatechange=c.noop}else if(!E&&x&&(x.readyState===4||q===\"timeout\")){E=true;x.onreadystatechange=c.noop;i=q===\"timeout\"?\"timeout\":!c.httpSuccess(x)?\"error\":e.ifModified&&c.httpNotModified(x,e.url)?\"notmodified\":\"success\";var p;if(i===\"success\")try{o=c.httpData(x,e.dataType,e)}catch(v){i=\"parsererror\";p=v}if(i===\"success\"||i===\"notmodified\")j||b();else c.handleError(e,x,i,p);d();q===\"timeout\"&&x.abort();if(e.async)x=null}};try{var h=x.abort;x.abort=function(){x&&h.call(x);\
g(\"abort\")}}catch(l){}e.async&&e.timeout>0&&setTimeout(function(){x&&!E&&g(\"timeout\")},e.timeout);try{x.send(n===\"POST\"||n===\"PUT\"||n===\"DELETE\"?e.data:null)}catch(m){c.handleError(e,x,null,m);d()}e.async||g();return x}},handleError:function(a,b,d,f){if(a.error)a.error.call(a.context||a,b,d,f);if(a.global)(a.context?c(a.context):c.event).trigger(\"ajaxError\",[b,a,f])},active:0,httpSuccess:function(a){try{return!a.status&&location.protocol===\"file:\"||a.status>=200&&a.status<300||a.status===304||a.status===\
1223||a.status===0}catch(b){}return false},httpNotModified:function(a,b){var d=a.getResponseHeader(\"Last-Modified\"),f=a.getResponseHeader(\"Etag\");if(d)c.lastModified[b]=d;if(f)c.etag[b]=f;return a.status===304||a.status===0},httpData:function(a,b,d){var f=a.getResponseHeader(\"content-type\")||\"\",e=b===\"xml\"||!b&&f.indexOf(\"xml\")>=0;a=e?a.responseXML:a.responseText;e&&a.documentElement.nodeName===\"parsererror\"&&c.error(\"parsererror\");if(d&&d.dataFilter)a=d.dataFilter(a,b);if(typeof a===\"string\")if(b===\
\"json\"||!b&&f.indexOf(\"json\")>=0)a=c.parseJSON(a);else if(b===\"script\"||!b&&f.indexOf(\"javascript\")>=0)c.globalEval(a);return a},param:function(a,b){function d(i,o){if(c.isArray(o))c.each(o,function(k,n){b||/\\[\\]$/.test(i)?f(i,n):d(i+\"[\"+(typeof n===\"object\"||c.isArray(n)?k:\"\")+\"]\",n)});else!b&&o!=null&&typeof o===\"object\"?c.each(o,function(k,n){d(i+\"[\"+k+\"]\",n)}):f(i,o)}function f(i,o){o=c.isFunction(o)?o():o;e[e.length]=encodeURIComponent(i)+\"=\"+encodeURIComponent(o)}var e=[];if(b===w)b=c.ajaxSettings.traditional;\
if(c.isArray(a)||a.jquery)c.each(a,function(){f(this.name,this.value)});else for(var j in a)d(j,a[j]);return e.join(\"&\").replace(yb,\"+\")}});var la={},Ab=/toggle|show|hide/,Bb=/^([+-]=)?([\\d+-.]+)(.*)$/,W,va=[[\"height\",\"marginTop\",\"marginBottom\",\"paddingTop\",\"paddingBottom\"],[\"width\",\"marginLeft\",\"marginRight\",\"paddingLeft\",\"paddingRight\"],[\"opacity\"]];c.fn.extend({show:function(a,b){if(a||a===0)return this.animate(K(\"show\",3),a,b);else{a=0;for(b=this.length;a<b;a++){var d=c.data(this[a],\"olddisplay\");\
this[a].style.display=d||\"\";if(c.css(this[a],\"display\")===\"none\"){d=this[a].nodeName;var f;if(la[d])f=la[d];else{var e=c(\"<\"+d+\" />\").appendTo(\"body\");f=e.css(\"display\");if(f===\"none\")f=\"block\";e.remove();la[d]=f}c.data(this[a],\"olddisplay\",f)}}a=0;for(b=this.length;a<b;a++)this[a].style.display=c.data(this[a],\"olddisplay\")||\"\";return this}},hide:function(a,b){if(a||a===0)return this.animate(K(\"hide\",3),a,b);else{a=0;for(b=this.length;a<b;a++){var d=c.data(this[a],\"olddisplay\");!d&&d!==\"none\"&&c.data(this[a],\
\"olddisplay\",c.css(this[a],\"display\"))}a=0;for(b=this.length;a<b;a++)this[a].style.display=\"none\";return this}},_toggle:c.fn.toggle,toggle:function(a,b){var d=typeof a===\"boolean\";if(c.isFunction(a)&&c.isFunction(b))this._toggle.apply(this,arguments);else a==null||d?this.each(function(){var f=d?a:c(this).is(\":hidden\");c(this)[f?\"show\":\"hide\"]()}):this.animate(K(\"toggle\",3),a,b);return this},fadeTo:function(a,b,d){return this.filter(\":hidden\").css(\"opacity\",0).show().end().animate({opacity:b},a,d)},\
animate:function(a,b,d,f){var e=c.speed(b,d,f);if(c.isEmptyObject(a))return this.each(e.complete);return this[e.queue===false?\"each\":\"queue\"](function(){var j=c.extend({},e),i,o=this.nodeType===1&&c(this).is(\":hidden\"),k=this;for(i in a){var n=i.replace(ia,ja);if(i!==n){a[n]=a[i];delete a[i];i=n}if(a[i]===\"hide\"&&o||a[i]===\"show\"&&!o)return j.complete.call(this);if((i===\"height\"||i===\"width\")&&this.style){j.display=c.css(this,\"display\");j.overflow=this.style.overflow}if(c.isArray(a[i])){(j.specialEasing=\
j.specialEasing||{})[i]=a[i][1];a[i]=a[i][0]}}if(j.overflow!=null)this.style.overflow=\"hidden\";j.curAnim=c.extend({},a);c.each(a,function(r,u){var z=new c.fx(k,j,r);if(Ab.test(u))z[u===\"toggle\"?o?\"show\":\"hide\":u](a);else{var C=Bb.exec(u),B=z.cur(true)||0;if(C){u=parseFloat(C[2]);var E=C[3]||\"px\";if(E!==\"px\"){k.style[r]=(u||1)+E;B=(u||1)/z.cur(true)*B;k.style[r]=B+E}if(C[1])u=(C[1]===\"-=\"?-1:1)*u+B;z.custom(B,u,E)}else z.custom(B,u,\"\")}});return true})},stop:function(a,b){var d=c.timers;a&&this.queue([]);\
this.each(function(){for(var f=d.length-1;f>=0;f--)if(d[f].elem===this){b&&d[f](true);d.splice(f,1)}});b||this.dequeue();return this}});c.each({slideDown:K(\"show\",1),slideUp:K(\"hide\",1),slideToggle:K(\"toggle\",1),fadeIn:{opacity:\"show\"},fadeOut:{opacity:\"hide\"}},function(a,b){c.fn[a]=function(d,f){return this.animate(b,d,f)}});c.extend({speed:function(a,b,d){var f=a&&typeof a===\"object\"?a:{complete:d||!d&&b||c.isFunction(a)&&a,duration:a,easing:d&&b||b&&!c.isFunction(b)&&b};f.duration=c.fx.off?0:typeof f.duration===\
\"number\"?f.duration:c.fx.speeds[f.duration]||c.fx.speeds._default;f.old=f.complete;f.complete=function(){f.queue!==false&&c(this).dequeue();c.isFunction(f.old)&&f.old.call(this)};return f},easing:{linear:function(a,b,d,f){return d+f*a},swing:function(a,b,d,f){return(-Math.cos(a*Math.PI)/2+0.5)*f+d}},timers:[],fx:function(a,b,d){this.options=b;this.elem=a;this.prop=d;if(!b.orig)b.orig={}}});c.fx.prototype={update:function(){this.options.step&&this.options.step.call(this.elem,this.now,this);(c.fx.step[this.prop]||\
c.fx.step._default)(this);if((this.prop===\"height\"||this.prop===\"width\")&&this.elem.style)this.elem.style.display=\"block\"},cur:function(a){if(this.elem[this.prop]!=null&&(!this.elem.style||this.elem.style[this.prop]==null))return this.elem[this.prop];return(a=parseFloat(c.css(this.elem,this.prop,a)))&&a>-10000?a:parseFloat(c.curCSS(this.elem,this.prop))||0},custom:function(a,b,d){function f(j){return e.step(j)}this.startTime=J();this.start=a;this.end=b;this.unit=d||this.unit||\"px\";this.now=this.start;\
this.pos=this.state=0;var e=this;f.elem=this.elem;if(f()&&c.timers.push(f)&&!W)W=setInterval(c.fx.tick,13)},show:function(){this.options.orig[this.prop]=c.style(this.elem,this.prop);this.options.show=true;this.custom(this.prop===\"width\"||this.prop===\"height\"?1:0,this.cur());c(this.elem).show()},hide:function(){this.options.orig[this.prop]=c.style(this.elem,this.prop);this.options.hide=true;this.custom(this.cur(),0)},step:function(a){var b=J(),d=true;if(a||b>=this.options.duration+this.startTime){this.now=\
this.end;this.pos=this.state=1;this.update();this.options.curAnim[this.prop]=true;for(var f in this.options.curAnim)if(this.options.curAnim[f]!==true)d=false;if(d){if(this.options.display!=null){this.elem.style.overflow=this.options.overflow;a=c.data(this.elem,\"olddisplay\");this.elem.style.display=a?a:this.options.display;if(c.css(this.elem,\"display\")===\"none\")this.elem.style.display=\"block\"}this.options.hide&&c(this.elem).hide();if(this.options.hide||this.options.show)for(var e in this.options.curAnim)c.style(this.elem,\
e,this.options.orig[e]);this.options.complete.call(this.elem)}return false}else{e=b-this.startTime;this.state=e/this.options.duration;a=this.options.easing||(c.easing.swing?\"swing\":\"linear\");this.pos=c.easing[this.options.specialEasing&&this.options.specialEasing[this.prop]||a](this.state,e,0,1,this.options.duration);this.now=this.start+(this.end-this.start)*this.pos;this.update()}return true}};c.extend(c.fx,{tick:function(){for(var a=c.timers,b=0;b<a.length;b++)a[b]()||a.splice(b--,1);a.length||\
c.fx.stop()},stop:function(){clearInterval(W);W=null},speeds:{slow:600,fast:200,_default:400},step:{opacity:function(a){c.style(a.elem,\"opacity\",a.now)},_default:function(a){if(a.elem.style&&a.elem.style[a.prop]!=null)a.elem.style[a.prop]=(a.prop===\"width\"||a.prop===\"height\"?Math.max(0,a.now):a.now)+a.unit;else a.elem[a.prop]=a.now}}});if(c.expr&&c.expr.filters)c.expr.filters.animated=function(a){return c.grep(c.timers,function(b){return a===b.elem}).length};c.fn.offset=\"getBoundingClientRect\"in s.documentElement?\
function(a){var b=this[0];if(a)return this.each(function(e){c.offset.setOffset(this,a,e)});if(!b||!b.ownerDocument)return null;if(b===b.ownerDocument.body)return c.offset.bodyOffset(b);var d=b.getBoundingClientRect(),f=b.ownerDocument;b=f.body;f=f.documentElement;return{top:d.top+(self.pageYOffset||c.support.boxModel&&f.scrollTop||b.scrollTop)-(f.clientTop||b.clientTop||0),left:d.left+(self.pageXOffset||c.support.boxModel&&f.scrollLeft||b.scrollLeft)-(f.clientLeft||b.clientLeft||0)}}:function(a){var b=\
this[0];if(a)return this.each(function(r){c.offset.setOffset(this,a,r)});if(!b||!b.ownerDocument)return null;if(b===b.ownerDocument.body)return c.offset.bodyOffset(b);c.offset.initialize();var d=b.offsetParent,f=b,e=b.ownerDocument,j,i=e.documentElement,o=e.body;f=(e=e.defaultView)?e.getComputedStyle(b,null):b.currentStyle;for(var k=b.offsetTop,n=b.offsetLeft;(b=b.parentNode)&&b!==o&&b!==i;){if(c.offset.supportsFixedPosition&&f.position===\"fixed\")break;j=e?e.getComputedStyle(b,null):b.currentStyle;\
k-=b.scrollTop;n-=b.scrollLeft;if(b===d){k+=b.offsetTop;n+=b.offsetLeft;if(c.offset.doesNotAddBorder&&!(c.offset.doesAddBorderForTableAndCells&&/^t(able|d|h)$/i.test(b.nodeName))){k+=parseFloat(j.borderTopWidth)||0;n+=parseFloat(j.borderLeftWidth)||0}f=d;d=b.offsetParent}if(c.offset.subtractsBorderForOverflowNotVisible&&j.overflow!==\"visible\"){k+=parseFloat(j.borderTopWidth)||0;n+=parseFloat(j.borderLeftWidth)||0}f=j}if(f.position===\"relative\"||f.position===\"static\"){k+=o.offsetTop;n+=o.offsetLeft}if(c.offset.supportsFixedPosition&&\
f.position===\"fixed\"){k+=Math.max(i.scrollTop,o.scrollTop);n+=Math.max(i.scrollLeft,o.scrollLeft)}return{top:k,left:n}};c.offset={initialize:function(){var a=s.body,b=s.createElement(\"div\"),d,f,e,j=parseFloat(c.curCSS(a,\"marginTop\",true))||0;c.extend(b.style,{position:\"absolute\",top:0,left:0,margin:0,border:0,width:\"1px\",height:\"1px\",visibility:\"hidden\"});b.innerHTML=\"<div style='position:absolute;top:0;left:0;margin:0;border:5px solid #000;padding:0;width:1px;height:1px;'><div></div></div><table style='position:absolute;top:0;left:0;margin:0;border:5px solid #000;padding:0;width:1px;height:1px;' cellpadding='0' cellspacing='0'><tr><td></td></tr></table>\";\
a.insertBefore(b,a.firstChild);d=b.firstChild;f=d.firstChild;e=d.nextSibling.firstChild.firstChild;this.doesNotAddBorder=f.offsetTop!==5;this.doesAddBorderForTableAndCells=e.offsetTop===5;f.style.position=\"fixed\";f.style.top=\"20px\";this.supportsFixedPosition=f.offsetTop===20||f.offsetTop===15;f.style.position=f.style.top=\"\";d.style.overflow=\"hidden\";d.style.position=\"relative\";this.subtractsBorderForOverflowNotVisible=f.offsetTop===-5;this.doesNotIncludeMarginInBodyOffset=a.offsetTop!==j;a.removeChild(b);\
c.offset.initialize=c.noop},bodyOffset:function(a){var b=a.offsetTop,d=a.offsetLeft;c.offset.initialize();if(c.offset.doesNotIncludeMarginInBodyOffset){b+=parseFloat(c.curCSS(a,\"marginTop\",true))||0;d+=parseFloat(c.curCSS(a,\"marginLeft\",true))||0}return{top:b,left:d}},setOffset:function(a,b,d){if(/static/.test(c.curCSS(a,\"position\")))a.style.position=\"relative\";var f=c(a),e=f.offset(),j=parseInt(c.curCSS(a,\"top\",true),10)||0,i=parseInt(c.curCSS(a,\"left\",true),10)||0;if(c.isFunction(b))b=b.call(a,\
d,e);d={top:b.top-e.top+j,left:b.left-e.left+i};\"using\"in b?b.using.call(a,d):f.css(d)}};c.fn.extend({position:function(){if(!this[0])return null;var a=this[0],b=this.offsetParent(),d=this.offset(),f=/^body|html$/i.test(b[0].nodeName)?{top:0,left:0}:b.offset();d.top-=parseFloat(c.curCSS(a,\"marginTop\",true))||0;d.left-=parseFloat(c.curCSS(a,\"marginLeft\",true))||0;f.top+=parseFloat(c.curCSS(b[0],\"borderTopWidth\",true))||0;f.left+=parseFloat(c.curCSS(b[0],\"borderLeftWidth\",true))||0;return{top:d.top-\
f.top,left:d.left-f.left}},offsetParent:function(){return this.map(function(){for(var a=this.offsetParent||s.body;a&&!/^body|html$/i.test(a.nodeName)&&c.css(a,\"position\")===\"static\";)a=a.offsetParent;return a})}});c.each([\"Left\",\"Top\"],function(a,b){var d=\"scroll\"+b;c.fn[d]=function(f){var e=this[0],j;if(!e)return null;if(f!==w)return this.each(function(){if(j=wa(this))j.scrollTo(!a?f:c(j).scrollLeft(),a?f:c(j).scrollTop());else this[d]=f});else return(j=wa(e))?\"pageXOffset\"in j?j[a?\"pageYOffset\":\
\"pageXOffset\"]:c.support.boxModel&&j.document.documentElement[d]||j.document.body[d]:e[d]}});c.each([\"Height\",\"Width\"],function(a,b){var d=b.toLowerCase();c.fn[\"inner\"+b]=function(){return this[0]?c.css(this[0],d,false,\"padding\"):null};c.fn[\"outer\"+b]=function(f){return this[0]?c.css(this[0],d,false,f?\"margin\":\"border\"):null};c.fn[d]=function(f){var e=this[0];if(!e)return f==null?null:this;if(c.isFunction(f))return this.each(function(j){var i=c(this);i[d](f.call(this,j,i[d]()))});return\"scrollTo\"in\
e&&e.document?e.document.compatMode===\"CSS1Compat\"&&e.document.documentElement[\"client\"+b]||e.document.body[\"client\"+b]:e.nodeType===9?Math.max(e.documentElement[\"client\"+b],e.body[\"scroll\"+b],e.documentElement[\"scroll\"+b],e.body[\"offset\"+b],e.documentElement[\"offset\"+b]):f===w?c.css(e,d):this.css(d,typeof f===\"string\"?f:f+\"px\")}});A.jQuery=A.$=c})(window);\
";
t262Libs["jquery.base64.js"] = "	\
	/**\
	 * jQuery BASE64 functions\
	 * \
	 * 	<code>\
	 * 		Encodes the given data with base64. \
	 * 		String $.base64Encode ( String str )\
	 *		<br />\
	 * 		Decodes a base64 encoded data.\
	 * 		String $.base64Decode ( String str )\
	 * 	</code>\
	 * \
	 * Encodes and Decodes the given data in base64.\
	 * This encoding is designed to make binary data survive transport through transport layers that are not 8-bit clean, such as mail bodies.\
	 * Base64-encoded data takes about 33% more space than the original data. \
	 * This javascript code is used to encode / decode data using base64 (this encoding is designed to make binary data survive transport through transport layers that are not 8-bit clean). Script is fully compatible with UTF-8 encoding. You can use base64 encoded data as simple encryption mechanism.\
	 * If you plan using UTF-8 encoding in your project don't forget to set the page encoding to UTF-8 (Content-Type meta tag). \
	 * This function orginally get from the WebToolkit and rewrite for using as the jQuery plugin.\
	 * \
	 * Example\
	 * 	Code\
	 * 		<code>\
	 * 			$.base64Encode(\"I'm Persian.\"); \
	 * 		</code>\
	 * 	Result\
	 * 		<code>\
	 * 			\"SSdtIFBlcnNpYW4u\"\
	 * 		</code>\
	 * 	Code\
	 * 		<code>\
	 * 			$.base64Decode(\"SSdtIFBlcnNpYW4u\");\
	 * 		</code>\
	 * 	Result\
	 * 		<code>\
	 * 			\"I'm Persian.\"\
	 * 		</code>\
	 * \
	 * @alias Muhammad Hussein Fattahizadeh < muhammad [AT] semnanweb [DOT] com >\
	 * @link http://www.semnanweb.com/jquery-plugin/base64.html\
	 * @see http://www.webtoolkit.info/\
	 * @license http://www.gnu.org/licenses/gpl.html [GNU General Public License]\
	 * @param {jQuery} {base64Encode:function(input))\
	 * @param {jQuery} {base64Decode:function(input))\
	 * @return string\
	 */\
	\
	(function($){\
		\
		var keyString = \"ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/=\";\
		\
		var uTF8Encode = function(string) {\
			string = string.replace(/\\x0d\\x0a/g, \"\\x0a\");\
			var output = \"\";\
			for (var n = 0; n < string.length; n++) {\
				var c = string.charCodeAt(n);\
				if (c < 128) {\
					output += String.fromCharCode(c);\
				} else if ((c > 127) && (c < 2048)) {\
					output += String.fromCharCode((c >> 6) | 192);\
					output += String.fromCharCode((c & 63) | 128);\
				} else {\
					output += String.fromCharCode((c >> 12) | 224);\
					output += String.fromCharCode(((c >> 6) & 63) | 128);\
					output += String.fromCharCode((c & 63) | 128);\
				}\
			}\
			return output;\
		};\
		\
		var uTF8Decode = function(input) {\
			var string = \"\";\
			var i = 0;\
			var c = c2 = c3 = c4 = 0;\
			while ( i < input.length ) {\
				c = input.charCodeAt(i);\
				if (c < 128) { // 1 byte encoding - ASCII only\
					string += String.fromCharCode(c);\
					i++;\
				} else if ((c >= 192) && (c < 224)) {  // 2 byte encoding - max U+07FF\
					c2 = input.charCodeAt(i+1);\
					string += String.fromCharCode(((c & 31) << 6) | (c2 & 63));\
					i += 2;\
				} else if ((c >= 224) && (c < 240)) {  // 3 byte encoding - max U+FFFF\
					c2 = input.charCodeAt(i+1);\
					c3 = input.charCodeAt(i+2);\
					string += String.fromCharCode(((c & 15) << 12) | ((c2 & 63) << 6) | (c3 & 63));\
					i += 3;\
				} else if ((c >= 240) && (c < 248)){  // 4 byte encoding - max U+10FFFF.  Covers all Unicode CodePoints\
					c2 = input.charCodeAt(i+1);\
					c3 = input.charCodeAt(i+2);\
					c4 = input.charCodeAt(i+3);\
					var codePoint = (((c & 7) << 18) | ((c2 & 63) << 12) | ((c3 & 63) << 6) | (c4 & 63));\
					if (codePoint > 0x10FFFF) {\
					    throw new SyntaxError(\"invalid UTF-8 code unit sequence\");\
					}\
					var highSurrogate = (((codePoint - 0x10000) & 0xFFC00) >>> 10) + 0xD800; // Minus 0x10000, then top 10 bits added to 0xD800\
					var lowSurrogate = ((codePoint - 0x10000) & 0x3FF) + 0xDC00; // Minus 0x10000, then low 10 bits added to 0xDC00\
					string += String.fromCharCode(highSurrogate);\
					string += String.fromCharCode(lowSurrogate);\
					i += 4;\
					\
				}\
			}\
			return string;\
		}\
		\
		$.extend({\
			base64Encode: function(input) {\
				var output = \"\";\
				var chr1, chr2, chr3, enc1, enc2, enc3, enc4;\
				var i = 0;\
				input = uTF8Encode(input);\
				while (i < input.length) {\
					chr1 = input.charCodeAt(i++);\
					chr2 = input.charCodeAt(i++);\
					chr3 = input.charCodeAt(i++);\
					enc1 = chr1 >> 2;\
					enc2 = ((chr1 & 3) << 4) | (chr2 >> 4);\
					enc3 = ((chr2 & 15) << 2) | (chr3 >> 6);\
					enc4 = chr3 & 63;\
					if (isNaN(chr2)) {\
						enc3 = enc4 = 64;\
					} else if (isNaN(chr3)) {\
						enc4 = 64;\
					}\
					output = output + keyString.charAt(enc1) + keyString.charAt(enc2) + keyString.charAt(enc3) + keyString.charAt(enc4);\
				}\
				return output;\
			},\
			base64Decode: function(input) {\
				var output = \"\";\
				var chr1, chr2, chr3;\
				var enc1, enc2, enc3, enc4;\
				var i = 0;\
				input = input.replace(/[^A-Za-z0-9\\+\\/\\=]/g, \"\");\
				while (i < input.length) {\
					enc1 = keyString.indexOf(input.charAt(i++));\
					enc2 = keyString.indexOf(input.charAt(i++));\
					enc3 = keyString.indexOf(input.charAt(i++));\
					enc4 = keyString.indexOf(input.charAt(i++));\
					chr1 = (enc1 << 2) | (enc2 >> 4);\
					chr2 = ((enc2 & 15) << 4) | (enc3 >> 2);\
					chr3 = ((enc3 & 3) << 6) | enc4;\
					output = output + String.fromCharCode(chr1);\
					if (enc3 != 64) {\
						output = output + String.fromCharCode(chr2);\
					}\
					if (enc4 != 64) {\
						output = output + String.fromCharCode(chr3);\
					}\
				}\
				output = uTF8Decode(output);\
				return output;\
			}\
		});\
	})(jQuery);\
";
t262Libs["jqueryprogressbar.js"] = "\
/*\
 * Copyright (c) 2007 Josh Bush (digitalbush.com)\
 * \
 * Permission is hereby granted, free of charge, to any person\
 * obtaining a copy of this software and associated documentation\
 * files (the \"Software\"), to deal in the Software without\
 * restriction, including without limitation the rights to use,\
 * copy, modify, merge, publish, distribute, sublicense, and/or sell\
 * copies of the Software, and to permit persons to whom the\
 * Software is furnished to do so, subject to the following\
 * conditions:\
\
 * The above copyright notice and this permission notice shall be\
 * included in all copies or substantial portions of the Software.\
 * \
 * THE SOFTWARE IS PROVIDED \"AS IS\", WITHOUT WARRANTY OF ANY KIND,\
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES\
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND\
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT\
 * HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,\
 * WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING\
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR\
 * OTHER DEALINGS IN THE SOFTWARE. \
 */\
 \
/*\
 * Progress Bar Plugin for jQuery\
 * Version: Alpha 2\
 * Release: 2007-02-26\
 */ \
(function($) {\
    //Main Method\
    $.fn.reportprogress = function(val, maxVal) {\
        var max = 100;\
        if (maxVal) {\
            max = maxVal;\
        }\
        return this.each(\
			function() {\
			    var div = $(this);\
			    var innerdiv = div.find(\".progress\");\
			    if (innerdiv.length !== 1) {\
			        innerdiv = $(\"<div class='progress'><span class='text'>&nbsp;</span></div>\");			        \
			        div.append(innerdiv);\
			    }\
			    var width = Math.round(val / max * 100);\
			    innerdiv.css(\"width\", width + \"%\");\
			    div.find(\".text\").html(width + \" %\");\
			}\
		);\
	};\
})(jQuery);\
";
t262Libs["math_isequal.js"] = "// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
var prec;\
function isEqual(num1, num2)\
{\
        if ((num1 === Infinity)&&(num2 === Infinity))\
        {\
                return(true);\
        }\
        if ((num1 === -Infinity)&&(num2 === -Infinity))\
        {\
                return(true);\
        }\
        prec = getPrecision(Math.min(Math.abs(num1), Math.abs(num2)));  \
        return(Math.abs(num1 - num2) <= prec);\
        //return(num1 === num2);\
}\
\
";
t262Libs["math_precision.js"] = "// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function getPrecision(num)\
{\
	//TODO: Create a table of prec's,\
	//      because using Math for testing Math isn't that correct. \
	\
	log2num = Math.log(Math.abs(num))/Math.LN2;\
	pernum = Math.ceil(log2num);\
	return(2 * Math.pow(2, -52 + pernum));\
	//return(0);\
}\
";
t262Libs["numeric_conversion.js"] = "// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function ToInteger(p) {\
  x = Number(p);\
\
  if(isNaN(x)){\
    return +0;\
  }\
  \
  if((x === +0) \
  || (x === -0) \
  || (x === Number.POSITIVE_INFINITY) \
  || (x === Number.NEGATIVE_INFINITY)){\
     return x;\
  }\
\
  var sign = ( x < 0 ) ? -1 : 1;\
\
  return (sign*Math.floor(Math.abs(x)));\
}\
";
t262Libs["sections.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
/* A section of the spec. Stores test results and subsections and some rolled up stats on how many tests passed or\
 * failed under that section\
 */\
function Section(parentSection, id, name) {\
    this.parentSection = parentSection;\
    this.id = id;\
    this.name = name;\
    this.subsections = {};\
    this.tests = [];\
    this.totalTests = 0;\
    this.totalPassed = 0;\
    this.totalFailed = 0;\
    this.totalFailedToLoad = 0;\
\
    var section = this,\
        RED_LIMIT = 50,\
        YELLOW_LIMIT = 75,\
        GREEN_LIMIT = 99.9;\
\
    /* Get the class for a result cell given the pass percent. */\
    function rollupCellClass(passPercent) {\
        if(passPercent >= GREEN_LIMIT) {\
            return \"reportGreen\";\
        } else if (passPercent >= YELLOW_LIMIT) {\
            return \"reportLightGreen\";\
        } else if (passPercent >= RED_LIMIT) {\
            return \"reportYellow\";\
        }\
\
        return \"reportRed\";\
    }\
\
    /* Calculate pass percent */\
    this.passPercent = function() {\
        if(this.totalTests === 0) {\
            return 0;\
        }\
\
        return Math.round((this.totalPassed / this.totalTests) * 100);\
    };\
\
    /* Add a test result to this section. Pushes the result to the\
     * test array and passes the result to addTestResult to tabulate\
     * pass/fail numbers\
     */\
    this.addTest = function(test) {\
        this.tests.push(test);\
        this.addTestResult(test);\
    };\
\
    /* Increments the various rollup counters for this section and all\
     * parent sections\
     */\
    this.addTestResult = function(test) {\
        this.totalTests++;\
\
        if(test.result === \"pass\")\
            this.totalPassed++;\
        else\
            this.totalFailed++;\
\
        if (test.error === 'Failed to load test case (probable parse error).')\
            this.totalFailedToLoad++;\
\
        if(this.parentSection !== null)\
            this.parentSection.addTestResult(test);\
    };\
\
    /* Renders this section as HTML. Used for the report page.*/\
    this.toHTML = function(options) {\
        var defaultOptions = {header: false, renderSubsections: true};\
\
        if (typeof options === undefined) {\
            options = defaultOptions;\
        } else {\
            options = $.extend(defaultOptions, options);\
        }\
\
        var html = '<tbody id=\"section_' + this.id.replace(/\\./g, \"_\") + '\">';\
\
        if(options.header) {\
            html += \"<tr><td class='tblHeader' colspan='3'>Chapter \" + this.id + \" - \" + this.name + \"</td>\" +\
                    \"<td class='\" + rollupCellClass(this.passPercent()) + \"'>\" + this.passPercent() + \"%</td></tr>\";\
        }\
\
        for(var i = 0; i < this.tests.length;i++) {\
            test = this.tests[i];\
            html += \"<tr><td>\" + test.id + \"</td>\" +\
                    \"<td>\" + test.description + \"</td>\" +\
                    \"<td><a class='showSource' href='#\" + test.id +\
                    \"'>[source]</a></td>\" +\
                    \"<td class='\" + test.result + \"'>\" + test.result +\
                    \"</td></tr>\";\
        }\
\
        for(var sectionId in this.subsections) {\
            var section = this.subsections[sectionId];\
\
            if(section.totalTests > 0) {\
                if(options.renderSubsections) {\
                    html += section.toHTML({\
                        header: true,\
                        renderSubsections: false});\
                } else {\
                    html += \"<tr><td colspan='3'><a class='section' href='#\" +\
                    section.id + \"'>Chapter \" + section.id + \" - \" +\
                    section.name + \"</a></td>\" +\
                            \"<td class='\" +\
                            rollupCellClass(section.passPercent()) + \"'>\" +\
                            section.passPercent() + \"%</td></tr>\";\
                }\
            }\
        }\
\
        return html + \"</tbody>\";\
    };\
\
    /* Render this section as XML. Used for the report page. */\
    this.toXML = function() {\
        var xml = \"\";\
        if(this.id != 0) {\
            xml += \"<section id='\" + this.id + \"' name='\" + this.name +\
                   \"'>\\r\\n\";\
\
            for (var i = 0; i < this.tests.length; i++) {\
                xml += '<test>\\r\\n' +\
                          '  <testId>' + this.tests[i].id + '</testId>\\r\\n' +\
                          '  <res>' + this.tests[i].result + '</res>\\r\\n' +\
                          '</test>\\r\\n';\
            }\
        }\
\
        for (var subsection in this.subsections) {\
            xml += this.subsections[subsection].toXML();\
        }\
\
        if(this.id != 0) {\
            xml += '</section>\\r\\n';\
        }\
\
        return xml;\
    };\
\
    /* Reset counts and remove tests. */\
    this.reset = function() {\
        this.tests = [];\
        this.totalTests = 0;\
        this.totalPassed = 0;\
        this.totalFailed = 0;\
        this.totalFailedToLoad = 0;\
\
        for(var subsection in this.subsections) {\
            this.subsections[subsection].reset();\
        }\
    };\
}\
";
t262Libs["sta.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
//-----------------------------------------------------------------------------\
function compareArray(aExpected, aActual) {\
    if (aActual.length != aExpected.length) {\
        return false;\
    }\
\
    aExpected.sort();\
    aActual.sort();\
\
    var s;\
    for (var i = 0; i < aExpected.length; i++) {\
        if (aActual[i] !== aExpected[i]) {\
            return false;\
        }\
    }\
    return true;\
}\
\
//-----------------------------------------------------------------------------\
function arrayContains(arr, expected) {\
    var found;\
    for (var i = 0; i < expected.length; i++) {\
        found = false;\
        for (var j = 0; j < arr.length; j++) {\
            if (expected[i] === arr[j]) {\
                found = true;\
                break;\
            }\
        }\
        if (!found) {\
            return false;\
        }\
    }\
    return true;\
}\
\
//-----------------------------------------------------------------------------\
var supportsArrayIndexGettersOnArrays = undefined;\
function fnSupportsArrayIndexGettersOnArrays() {\
    if (typeof supportsArrayIndexGettersOnArrays !== \"undefined\") {\
        return supportsArrayIndexGettersOnArrays;\
    }\
\
    supportsArrayIndexGettersOnArrays = false;\
\
    if (fnExists(Object.defineProperty)) {\
        var arr = [];\
        Object.defineProperty(arr, \"0\", {\
            get: function() {\
                supportsArrayIndexGettersOnArrays = true;\
                return 0;\
            }\
        });\
        var res = arr[0];\
    }\
\
    return supportsArrayIndexGettersOnArrays;\
}\
\
//-----------------------------------------------------------------------------\
var supportsArrayIndexGettersOnObjects = undefined;\
function fnSupportsArrayIndexGettersOnObjects() {\
    if (typeof supportsArrayIndexGettersOnObjects !== \"undefined\")\
        return supportsArrayIndexGettersOnObjects;\
\
    supportsArrayIndexGettersOnObjects = false;\
\
    if (fnExists(Object.defineProperty)) {\
        var obj = {};\
        Object.defineProperty(obj, \"0\", {\
            get: function() {\
                supportsArrayIndexGettersOnObjects = true;\
                return 0;\
            }\
        });\
        var res = obj[0];\
    }\
\
    return supportsArrayIndexGettersOnObjects;\
}\
\
//-----------------------------------------------------------------------------\
function ConvertToFileUrl(pathStr) {\
    return \"file:\" + pathStr.replace(/\\\\/g, \"/\");\
}\
\
//-----------------------------------------------------------------------------\
function fnExists(/*arguments*/) {\
    for (var i = 0; i < arguments.length; i++) {\
        if (typeof (arguments[i]) !== \"function\") return false;\
    }\
    return true;\
}\
\
//-----------------------------------------------------------------------------\
var __globalObject = Function(\"return this;\")();\
function fnGlobalObject() {\
     return __globalObject;\
}\
\
//-----------------------------------------------------------------------------\
function fnSupportsStrict() {\
    \"use strict\";\
    try {\
        eval('with ({}) {}');\
        return false;\
    } catch (e) {\
        return true;\
    }\
}\
\
//-----------------------------------------------------------------------------\
//Verify all attributes specified data property of given object:\
//value, writable, enumerable, configurable\
//If all attribute values are expected, return true, otherwise, return false\
function dataPropertyAttributesAreCorrect(obj,\
                                          name,\
                                          value,\
                                          writable,\
                                          enumerable,\
                                          configurable) {\
    var attributesCorrect = true;\
\
    if (obj[name] !== value) {\
        if (typeof obj[name] === \"number\" &&\
            isNaN(obj[name]) &&\
            typeof value === \"number\" &&\
            isNaN(value)) {\
            // keep empty\
        } else {\
            attributesCorrect = false;\
        }\
    }\
\
    try {\
        if (obj[name] === \"oldValue\") {\
            obj[name] = \"newValue\";\
        } else {\
            obj[name] = \"OldValue\";\
        }\
    } catch (we) {\
    }\
\
    var overwrited = false;\
    if (obj[name] !== value) {\
        if (typeof obj[name] === \"number\" &&\
            isNaN(obj[name]) &&\
            typeof value === \"number\" &&\
            isNaN(value)) {\
            // keep empty\
        } else {\
            overwrited = true;\
        }\
    }\
    if (overwrited !== writable) {\
        attributesCorrect = false;\
    }\
\
    var enumerated = false;\
    for (var prop in obj) {\
        if (obj.hasOwnProperty(prop) && prop === name) {\
            enumerated = true;\
        }\
    }\
\
    if (enumerated !== enumerable) {\
        attributesCorrect = false;\
    }\
\
\
    var deleted = false;\
\
    try {\
        delete obj[name];\
    } catch (de) {\
    }\
    if (!obj.hasOwnProperty(name)) {\
        deleted = true;\
    }\
    if (deleted !== configurable) {\
        attributesCorrect = false;\
    }\
\
    return attributesCorrect;\
}\
\
//-----------------------------------------------------------------------------\
//Verify all attributes specified accessor property of given object:\
//get, set, enumerable, configurable\
//If all attribute values are expected, return true, otherwise, return false\
function accessorPropertyAttributesAreCorrect(obj,\
                                              name,\
                                              get,\
                                              set,\
                                              setVerifyHelpProp,\
                                              enumerable,\
                                              configurable) {\
    var attributesCorrect = true;\
\
    if (get !== undefined) {\
        if (obj[name] !== get()) {\
            if (typeof obj[name] === \"number\" &&\
                isNaN(obj[name]) &&\
                typeof get() === \"number\" &&\
                isNaN(get())) {\
                // keep empty\
            } else {\
                attributesCorrect = false;\
            }\
        }\
    } else {\
        if (obj[name] !== undefined) {\
            attributesCorrect = false;\
        }\
    }\
\
    try {\
        var desc = Object.getOwnPropertyDescriptor(obj, name);\
        if (typeof desc.set === \"undefined\") {\
            if (typeof set !== \"undefined\") {\
                attributesCorrect = false;\
            }\
        } else {\
            obj[name] = \"toBeSetValue\";\
            if (obj[setVerifyHelpProp] !== \"toBeSetValue\") {\
                attributesCorrect = false;\
            }\
        }\
    } catch (se) {\
        throw se;\
    }\
\
\
    var enumerated = false;\
    for (var prop in obj) {\
        if (obj.hasOwnProperty(prop) && prop === name) {\
            enumerated = true;\
        }\
    }\
\
    if (enumerated !== enumerable) {\
        attributesCorrect = false;\
    }\
\
\
    var deleted = false;\
    try {\
        delete obj[name];\
    } catch (de) {\
        throw de;\
    }\
    if (!obj.hasOwnProperty(name)) {\
        deleted = true;\
    }\
    if (deleted !== configurable) {\
        attributesCorrect = false;\
    }\
\
    return attributesCorrect;\
}\
\
//-----------------------------------------------------------------------------\
var NotEarlyErrorString = \"NotEarlyError\";\
var EarlyErrorRePat = \"^((?!\" + NotEarlyErrorString + \").)*$\";\
var NotEarlyError = new Error(NotEarlyErrorString);\
\
//-----------------------------------------------------------------------------\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function Test262Error(message) {\
    if (message) this.message = message;\
}\
\
Test262Error.prototype.toString = function () {\
    return \"Test262 Error: \" + this.message;\
};\
\
function testFailed(message) {\
    throw new Test262Error(message);\
}\
\
\
function testPrint(message) {\
\
}\
\
\
//adaptors for Test262 framework\
function $PRINT(message) {\
\
}\
\
function $INCLUDE(message) { }\
function $ERROR(message) {\
    testFailed(message);\
}\
\
function $FAIL(message) {\
    testFailed(message);\
}\
\
\
\
//Sputnik library definitions\
//Ultimately these should be namespaced some how and only made\
//available to tests that explicitly include them.\
//For now, we just define the globally\
\
//math_precision.js\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function getPrecision(num) {\
    //TODO: Create a table of prec's,\
    //      because using Math for testing Math isn't that correct.\
\
    var log2num = Math.log(Math.abs(num)) / Math.LN2;\
    var pernum = Math.ceil(log2num);\
    return (2 * Math.pow(2, -52 + pernum));\
    //return(0);\
}\
\
\
//math_isequal.js\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
var prec;\
function isEqual(num1, num2) {\
    if ((num1 === Infinity) && (num2 === Infinity)) {\
        return (true);\
    }\
    if ((num1 === -Infinity) && (num2 === -Infinity)) {\
        return (true);\
    }\
    prec = getPrecision(Math.min(Math.abs(num1), Math.abs(num2)));\
    return (Math.abs(num1 - num2) <= prec);\
    //return(num1 === num2);\
}\
\
//numeric_conversion.js\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
function ToInteger(p) {\
    var x = Number(p);\
\
    if (isNaN(x)) {\
        return +0;\
    }\
\
    if ((x === +0)\
  || (x === -0)\
  || (x === Number.POSITIVE_INFINITY)\
  || (x === Number.NEGATIVE_INFINITY)) {\
        return x;\
    }\
\
    var sign = (x < 0) ? -1 : 1;\
\
    return (sign * Math.floor(Math.abs(x)));\
}\
\
//Date_constants.js\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
var HoursPerDay = 24;\
var MinutesPerHour = 60;\
var SecondsPerMinute = 60;\
\
var msPerDay = 86400000;\
var msPerSecond = 1000;\
var msPerMinute = 60000;\
var msPerHour = 3600000;\
\
var date_1899_end = -2208988800001;\
var date_1900_start = -2208988800000;\
var date_1969_end = -1;\
var date_1970_start = 0;\
var date_1999_end = 946684799999;\
var date_2000_start = 946684800000;\
var date_2099_end = 4102444799999;\
var date_2100_start = 4102444800000;\
\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
//the following values are normally generated by the sputnik.py driver\
var $LocalTZ,\
    $DST_start_month,\
    $DST_start_sunday,\
    $DST_start_hour,\
    $DST_start_minutes,\
    $DST_end_month,\
    $DST_end_sunday,\
    $DST_end_hour,\
    $DST_end_minutes;\
\
(function () {\
    /**\
      * Finds the first date, starting from |start|, where |predicate|\
      * holds.\
      */\
    var findNearestDateBefore = function(start, predicate) {\
        var current = start;\
        var month = 1000 * 60 * 60 * 24 * 30;\
        for (var step = month; step > 0; step = Math.floor(step / 3)) {\
            if (!predicate(current)) {\
                while (!predicate(current))\
                    current = new Date(current.getTime() + step);\
                    current = new Date(current.getTime() - step);\
                }\
        }\
        while (!predicate(current)) {\
            current = new Date(current.getTime() + 1);\
        }\
        return current;\
    };\
\
    var juneDate = new Date(2000, 5, 20, 0, 0, 0, 0);\
    var decemberDate = new Date(2000, 11, 20, 0, 0, 0, 0);\
    var juneOffset = juneDate.getTimezoneOffset();\
    var decemberOffset = decemberDate.getTimezoneOffset();\
    var isSouthernHemisphere = (juneOffset > decemberOffset);\
    var winterTime = isSouthernHemisphere ? juneDate : decemberDate;\
    var summerTime = isSouthernHemisphere ? decemberDate : juneDate;\
\
    var dstStart = findNearestDateBefore(winterTime, function (date) {\
        return date.getTimezoneOffset() == summerTime.getTimezoneOffset();\
    });\
    $DST_start_month = dstStart.getMonth();\
    $DST_start_sunday = dstStart.getDate() > 15 ? '\"last\"' : '\"first\"';\
    $DST_start_hour = dstStart.getHours();\
    $DST_start_minutes = dstStart.getMinutes();\
\
    var dstEnd = findNearestDateBefore(summerTime, function (date) {\
        return date.getTimezoneOffset() == winterTime.getTimezoneOffset();\
    });\
    $DST_end_month = dstEnd.getMonth();\
    $DST_end_sunday = dstEnd.getDate() > 15 ? '\"last\"' : '\"first\"';\
    $DST_end_hour = dstEnd.getHours();\
    $DST_end_minutes = dstEnd.getMinutes();\
\
    return;\
})();\
\
\
//Date.library.js\
// Copyright 2009 the Sputnik authors.  All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
//15.9.1.2 Day Number and Time within Day\
function Day(t) {\
  return Math.floor(t/msPerDay);\
}\
\
function TimeWithinDay(t) {\
  return t%msPerDay;\
}\
\
//15.9.1.3 Year Number\
function DaysInYear(y){\
  if(y%4 != 0) return 365;\
  if(y%4 == 0 && y%100 != 0) return 366;\
  if(y%100 == 0 && y%400 != 0) return 365;\
  if(y%400 == 0) return 366;\
}\
\
function DayFromYear(y) {\
  return (365*(y-1970)\
          + Math.floor((y-1969)/4)\
          - Math.floor((y-1901)/100)\
          + Math.floor((y-1601)/400));\
}\
\
function TimeFromYear(y){\
  return msPerDay*DayFromYear(y);\
}\
\
function YearFromTime(t) {\
  t = Number(t);\
  var sign = ( t < 0 ) ? -1 : 1;\
  var year = ( sign < 0 ) ? 1969 : 1970;\
\
  for(var time = 0;;year += sign){\
    time = TimeFromYear(year);\
\
    if(sign > 0 && time > t){\
      year -= sign;\
      break;\
    }\
    else if(sign < 0 && time <= t){\
      break;\
    }\
  };\
  return year;\
}\
\
function InLeapYear(t){\
  if(DaysInYear(YearFromTime(t)) == 365)\
    return 0;\
\
  if(DaysInYear(YearFromTime(t)) == 366)\
    return 1;\
}\
\
function DayWithinYear(t) {\
  return Day(t)-DayFromYear(YearFromTime(t));\
}\
\
//15.9.1.4 Month Number\
function MonthFromTime(t){\
  var day = DayWithinYear(t);\
  var leap = InLeapYear(t);\
\
  if((0 <= day) && (day < 31)) return 0;\
  if((31 <= day) && (day < (59+leap))) return 1;\
  if(((59+leap) <= day) && (day < (90+leap))) return 2;\
  if(((90+leap) <= day) && (day < (120+leap))) return 3;\
  if(((120+leap) <= day) && (day < (151+leap))) return 4;\
  if(((151+leap) <= day) && (day < (181+leap))) return 5;\
  if(((181+leap) <= day) && (day < (212+leap))) return 6;\
  if(((212+leap) <= day) && (day < (243+leap))) return 7;\
  if(((243+leap) <= day) && (day < (273+leap))) return 8;\
  if(((273+leap) <= day) && (day < (304+leap))) return 9;\
  if(((304+leap) <= day) && (day < (334+leap))) return 10;\
  if(((334+leap) <= day) && (day < (365+leap))) return 11;\
}\
\
//15.9.1.5 Date Number\
function DateFromTime(t) {\
  var day = DayWithinYear(t);\
  var month = MonthFromTime(t);\
  var leap = InLeapYear(t);\
\
  if(month == 0) return day+1;\
  if(month == 1) return day-30;\
  if(month == 2) return day-58-leap;\
  if(month == 3) return day-89-leap;\
  if(month == 4) return day-119-leap;\
  if(month == 5) return day-150-leap;\
  if(month == 6) return day-180-leap;\
  if(month == 7) return day-211-leap;\
  if(month == 8) return day-242-leap;\
  if(month == 9) return day-272-leap;\
  if(month == 10) return day-303-leap;\
  if(month == 11) return day-333-leap;\
}\
\
//15.9.1.6 Week Day\
function WeekDay(t) {\
  var weekday = (Day(t)+4)%7;\
  return (weekday < 0 ? 7+weekday : weekday);\
}\
\
//15.9.1.9 Daylight Saving Time Adjustment\
$LocalTZ = (new Date()).getTimezoneOffset() / -60;\
if (DaylightSavingTA((new Date()).valueOf()) !== 0) {\
   $LocalTZ -= 1;\
}\
var LocalTZA = $LocalTZ*msPerHour;\
\
function DaysInMonth(m, leap) {\
  m = m%12;\
\
  //April, June, Sept, Nov\
  if(m == 3 || m == 5 || m == 8 || m == 10 ) {\
    return 30;\
  }\
\
  //Jan, March, May, July, Aug, Oct, Dec\
  if(m == 0 || m == 2 || m == 4 || m == 6 || m == 7 || m == 9 || m == 11){\
    return 31;\
  }\
\
  //Feb\
  return 28+leap;\
}\
\
function GetSundayInMonth(t, m, count){\
    var year = YearFromTime(t);\
    var tempDate;\
\
    if (count==='\"first\"') {\
        for (var d=1; d <= DaysInMonth(m, InLeapYear(t)); d++) {\
            tempDate = new Date(year, m, d);\
            if (tempDate.getDay()===0) {\
                return tempDate.valueOf();\
            }\
        }\
    } else if(count==='\"last\"') {\
        for (var d=DaysInMonth(m, InLeapYear(t)); d>0; d--) {\
            tempDate = new Date(year, m, d);\
            if (tempDate.getDay()===0) {\
                return tempDate.valueOf();\
            }\
        }\
    }\
    throw new Error(\"Unsupported 'count' arg:\" + count);\
}\
/*\
function GetSundayInMonth(t, m, count){\
  var year = YearFromTime(t);\
  var leap = InLeapYear(t);\
  var day = 0;\
\
  if(m >= 1) day += DaysInMonth(0, leap);\
  if(m >= 2) day += DaysInMonth(1, leap);\
  if(m >= 3) day += DaysInMonth(2, leap);\
  if(m >= 4) day += DaysInMonth(3, leap);\
  if(m >= 5) day += DaysInMonth(4, leap);\
  if(m >= 6) day += DaysInMonth(5, leap);\
  if(m >= 7) day += DaysInMonth(6, leap);\
  if(m >= 8) day += DaysInMonth(7, leap);\
  if(m >= 9) day += DaysInMonth(8, leap);\
  if(m >= 10) day += DaysInMonth(9, leap);\
  if(m >= 11) day += DaysInMonth(10, leap);\
\
  var month_start = TimeFromYear(year)+day*msPerDay;\
  var sunday = 0;\
\
  if(count === \"last\"){\
    for(var last_sunday = month_start+DaysInMonth(m, leap)*msPerDay;\
      WeekDay(last_sunday)>0;\
      last_sunday -= msPerDay\
    ){};\
    sunday = last_sunday;\
  }\
  else {\
    for(var first_sunday = month_start;\
      WeekDay(first_sunday)>0;\
      first_sunday += msPerDay\
    ){};\
    sunday = first_sunday+7*msPerDay*(count-1);\
  }\
\
  return sunday;\
}*/\
\
function DaylightSavingTA(t) {\
//  t = t-LocalTZA;\
\
  var DST_start = GetSundayInMonth(t, $DST_start_month, $DST_start_sunday) +\
                  $DST_start_hour*msPerHour +\
                  $DST_start_minutes*msPerMinute;\
\
  var k = new Date(DST_start);\
\
  var DST_end   = GetSundayInMonth(t, $DST_end_month, $DST_end_sunday) +\
                  $DST_end_hour*msPerHour +\
                  $DST_end_minutes*msPerMinute;\
\
  if ( t >= DST_start && t < DST_end ) {\
    return msPerHour;\
  } else {\
    return 0;\
  }\
}\
\
//15.9.1.9 Local Time\
function LocalTime(t){\
  return t+LocalTZA+DaylightSavingTA(t);\
}\
\
function UTC(t) {\
  return t-LocalTZA-DaylightSavingTA(t-LocalTZA);\
}\
\
//15.9.1.10 Hours, Minutes, Second, and Milliseconds\
function HourFromTime(t){\
  return Math.floor(t/msPerHour)%HoursPerDay;\
}\
\
function MinFromTime(t){\
  return Math.floor(t/msPerMinute)%MinutesPerHour;\
}\
\
function SecFromTime(t){\
  return Math.floor(t/msPerSecond)%SecondsPerMinute;\
}\
\
function msFromTime(t){\
  return t%msPerSecond;\
}\
\
//15.9.1.11 MakeTime (hour, min, sec, ms)\
function MakeTime(hour, min, sec, ms){\
  if ( !isFinite(hour) || !isFinite(min) || !isFinite(sec) || !isFinite(ms)) {\
    return Number.NaN;\
  }\
\
  hour = ToInteger(hour);\
  min  = ToInteger(min);\
  sec  = ToInteger(sec);\
  ms   = ToInteger(ms);\
\
  return ((hour*msPerHour) + (min*msPerMinute) + (sec*msPerSecond) + ms);\
}\
\
//15.9.1.12 MakeDay (year, month, date)\
function MakeDay(year, month, date) {\
  if ( !isFinite(year) || !isFinite(month) || !isFinite(date)) {\
    return Number.NaN;\
  }\
\
  year = ToInteger(year);\
  month = ToInteger(month);\
  date = ToInteger(date );\
\
  var result5 = year + Math.floor(month/12);\
  var result6 = month%12;\
\
  var sign = ( year < 1970 ) ? -1 : 1;\
  var t =    ( year < 1970 ) ? 1 :  0;\
  var y =    ( year < 1970 ) ? 1969 : 1970;\
\
  if( sign == -1 ){\
    for ( y = 1969; y >= year; y += sign ) {\
      t += sign * DaysInYear(y)*msPerDay;\
    }\
  } else {\
    for ( y = 1970 ; y < year; y += sign ) {\
      t += sign * DaysInYear(y)*msPerDay;\
    }\
  }\
\
  var leap = 0;\
  for ( var m = 0; m < month; m++ ) {\
    //if year is changed, than we need to recalculate leep\
    leap = InLeapYear(t);\
    t += DaysInMonth(m, leap)*msPerDay;\
  }\
\
  if ( YearFromTime(t) != result5 ) {\
    return Number.NaN;\
  }\
  if ( MonthFromTime(t) != result6 ) {\
    return Number.NaN;\
  }\
  if ( DateFromTime(t) != 1 ) {\
    return Number.NaN;\
  }\
\
  return Day(t)+date-1;\
}\
\
//15.9.1.13 MakeDate (day, time)\
function MakeDate( day, time ) {\
  if(!isFinite(day) || !isFinite(time)) {\
    return Number.NaN;\
  }\
\
  return day*msPerDay+time;\
}\
\
//15.9.1.14 TimeClip (time)\
function TimeClip(time) {\
  if(!isFinite(time) || Math.abs(time) > 8.64e15){\
    return Number.NaN;\
  }\
\
  return ToInteger(time);\
}\
\
//Test Functions\
//ConstructDate is considered deprecated, and should not be used directly from\
//test262 tests as it's incredibly sensitive to DST start/end dates that \
//vary with geographic location.\
function ConstructDate(year, month, date, hours, minutes, seconds, ms){\
  /*\
   * 1. Call ToNumber(year)\
   * 2. Call ToNumber(month)\
   * 3. If date is supplied use ToNumber(date); else use 1\
   * 4. If hours is supplied use ToNumber(hours); else use 0\
   * 5. If minutes is supplied use ToNumber(minutes); else use 0\
   * 6. If seconds is supplied use ToNumber(seconds); else use 0\
   * 7. If ms is supplied use ToNumber(ms); else use 0\
   * 8. If Result(1) is not NaN and 0 <= ToInteger(Result(1)) <= 99, Result(8) is\
   * 1900+ToInteger(Result(1)); otherwise, Result(8) is Result(1)\
   * 9. Compute MakeDay(Result(8), Result(2), Result(3))\
   * 10. Compute MakeTime(Result(4), Result(5), Result(6), Result(7))\
   * 11. Compute MakeDate(Result(9), Result(10))\
   * 12. Set the [[Value]] property of the newly constructed object to TimeClip(UTC(Result(11)))\
   */\
  var r1 = Number(year);\
  var r2 = Number(month);\
  var r3 = ((date && arguments.length > 2) ? Number(date) : 1);\
  var r4 = ((hours && arguments.length > 3) ? Number(hours) : 0);\
  var r5 = ((minutes && arguments.length > 4) ? Number(minutes) : 0);\
  var r6 = ((seconds && arguments.length > 5) ? Number(seconds) : 0);\
  var r7 = ((ms && arguments.length > 6) ? Number(ms) : 0);\
\
  var r8 = r1;\
\
  if(!isNaN(r1) && (0 <= ToInteger(r1)) && (ToInteger(r1) <= 99))\
    r8 = 1900+r1;\
\
  var r9 = MakeDay(r8, r2, r3);\
  var r10 = MakeTime(r4, r5, r6, r7);\
  var r11 = MakeDate(r9, r10);\
\
  var retVal = TimeClip(UTC(r11));\
  return retVal;\
}\
\
\
\
/**** Python code for initialize the above constants\
// We may want to replicate the following in JavaScript.\
// However, using JS date operations to generate parameters that are then used to\
// test those some date operations seems unsound.  However, it isn't clear if there\
//is a good interoperable alternative.\
\
# Copyright 2009 the Sputnik authors.  All rights reserved.\
# This code is governed by the BSD license found in the LICENSE file.\
\
def GetDaylightSavingsTimes():\
# Is the given floating-point time in DST?\
def IsDst(t):\
return time.localtime(t)[-1]\
# Binary search to find an interval between the two times no greater than\
# delta where DST switches, returning the midpoint.\
def FindBetween(start, end, delta):\
while end - start > delta:\
middle = (end + start) / 2\
if IsDst(middle) == IsDst(start):\
start = middle\
else:\
end = middle\
return (start + end) / 2\
now = time.time()\
one_month = (30 * 24 * 60 * 60)\
# First find a date with different daylight savings.  To avoid corner cases\
# we try four months before and after today.\
after = now + 4 * one_month\
before = now - 4 * one_month\
if IsDst(now) == IsDst(before) and IsDst(now) == IsDst(after):\
logger.warning(\"Was unable to determine DST info.\")\
return None\
# Determine when the change occurs between now and the date we just found\
# in a different DST.\
if IsDst(now) != IsDst(before):\
first = FindBetween(before, now, 1)\
else:\
first = FindBetween(now, after, 1)\
# Determine when the change occurs between three and nine months from the\
# first.\
second = FindBetween(first + 3 * one_month, first + 9 * one_month, 1)\
# Find out which switch is into and which if out of DST\
if IsDst(first - 1) and not IsDst(first + 1):\
start = second\
end = first\
else:\
start = first\
end = second\
return (start, end)\
\
\
def GetDaylightSavingsAttribs():\
times = GetDaylightSavingsTimes()\
if not times:\
return None\
(start, end) = times\
def DstMonth(t):\
return time.localtime(t)[1] - 1\
def DstHour(t):\
return time.localtime(t - 1)[3] + 1\
def DstSunday(t):\
if time.localtime(t)[2] > 15:\
return \"'last'\"\
else:\
return \"'first'\"\
def DstMinutes(t):\
return (time.localtime(t - 1)[4] + 1) % 60\
attribs = { }\
attribs['start_month'] = DstMonth(start)\
attribs['end_month'] = DstMonth(end)\
attribs['start_sunday'] = DstSunday(start)\
attribs['end_sunday'] = DstSunday(end)\
attribs['start_hour'] = DstHour(start)\
attribs['end_hour'] = DstHour(end)\
attribs['start_minutes'] = DstMinutes(start)\
attribs['end_minutes'] = DstMinutes(end)\
return attribs\
\
*********/\
\
//--Test case registration-----------------------------------------------------\
function runTestCase(testcase) {\
    if (testcase() !== true) {\
        $ERROR(\"Test case returned non-true value!\");\
    }\
}\
";
t262Libs["sth.js"] = "/// Copyright (c) 2012 Ecma International.  All rights reserved. \
/// Ecma International makes this code available under the terms and conditions set\
/// forth on http://hg.ecmascript.org/tests/test262/raw-file/tip/LICENSE (the \
/// \"Use Terms\").   Any redistribution of this code must retain the above \
/// copyright and this notice and otherwise comply with the Use Terms.\
\
// Do not cache any JSON files - see\
// https://bugs.ecmascript.org/show_bug.cgi?id=87\
$.ajaxSetup( {cache:false});\
\
/*\
 * Run a test in the browser. Works by injecting an iframe with the test code.\
 *\
 * Public Methods:\
 * * run(id, test): Runs the test specified.\
 *\
 * Callbacks:\
 * * onComplete(test): Called when the test is run. Test object\
 *                     contains result and error strings describing how the\
 *                     test ran.\
 */\
function BrowserRunner() {\
    var iframe,             // injected iframe\
        currentTest,        // Current test being run.\
        scriptCache = {},   // Holds the various includes required to run certain tests.\
        instance    = this,\
        errorDetectorFileContents,\
        simpleTestAPIContents,\
        globalScopeContents,\
        harnessDir = \"harness/\";\
\
    $.ajax({async: false,\
            dataType: \"text\",\
            success: function(data){errorDetectorFileContents = data;},\
            url:harnessDir+\"ed.js\"});\
\
    $.ajax({async: false,\
            dataType: \"text\",\
            success: function(data){simpleTestAPIContents = data;},\
            url:harnessDir+\"sta.js\"});\
\
    $.ajax({async: false,\
            dataType: \"text\",\
            success: function(data){globalScopeContents = data;},\
            url:harnessDir+\"gs.js\"});\
\
    /* Called by the child window to notify that the test has\
     * finished. This function call is put in a separate script block\
     * at the end of the page so errors in the test script block\
     * should not prevent this function from being called.\
     */\
    function testFinished() {\
        if((typeof currentTest.result) === \"undefined\") {\
            // We didn't get a call to testRun, which likely means the\
            // test failed to load.\
            currentTest.result = \"fail\";\
            currentTest.error  = \"Failed to load test case (probable parse error).\";\
            currentTest.description = \"Failed to load test case!\";\
        } else if((typeof currentTest.error) !== \"undefined\") {\
            // We have an error logged from testRun.\
            if(currentTest.error instanceof Test262Error) {\
                currentTest.error = currentTest.message;\
            } else {\
            currentTest.error = currentTest.error.name + \": \" + currentTest.error.message;\
            }\
        } else if ((typeof currentTest.error === \"undefined\") && (currentTest.result === \"fail\")) {\
            currentTest.error = \"Test case returned non-true value.\";\
        }\
\
        document.body.removeChild(iframe);\
\
        instance.onComplete(currentTest);\
    }\
\
    /* Called from the child window after the test has run. */\
    function testRun(id, path, description, codeString, result, error) {\
        currentTest.id = id;\
        currentTest.path = path;\
        currentTest.description = description;\
        currentTest.result = result;\
        currentTest.error = error;\
        currentTest.code = codeString;\
    }\
\
\
    /* Run the test. */\
    this.run = function (test, code) {\
        var start = new Date();\
        \
        //--Detect proper window.onerror support\
        if (instance.supportsWindowOnerror===undefined) {\
            var iframePrereqs = document.createElement(\"iframe\");\
            iframePrereqs.setAttribute(\"id\", \"prereqsIframe\");\
            if (!/firefox/i.test(navigator.userAgent)) {\
                iframePrereqs.setAttribute(\"style\", \"display:none\");\
            }\
            document.body.appendChild(iframePrereqs);\
\
            var iwinPrereqs = iframePrereqs.contentWindow; \
            var idocPrereqs = iwinPrereqs.document;\
            idocPrereqs.open();\
    \
            iwinPrereqs.failCount = 0;\
            \
            var stuff = [\
                         \"window.onerror = function(a, b, c) { this.failCount++; }\",\
                         \"va xyz =\",\
                         \"throw Error();\"\
            ];\
    \
            for(var i in stuff) {\
                idocPrereqs.writeln(\"<script type='text/javascript'>\");\
                idocPrereqs.writeln(stuff[i]);\
                idocPrereqs.writeln(\"</script>\");\
            }\
            idocPrereqs.close();\
            \
            //TODO - 500ms *should* be a sufficient delay\
            setTimeout(function() {\
                instance.supportsWindowOnerror = iwinPrereqs.failCount === 2;\
                //alert(iwinPrereqs.failCount);\
                document.body.removeChild(iframePrereqs);\
                instance.run(test, code);\
            }, 500);\
            return 0; // initial config, ignore this timing.\
        }\
        \
        currentTest = {};\
        for (var tempIndex in test) {\
            if (test.hasOwnProperty(tempIndex)) {\
                currentTest[tempIndex] = test[tempIndex];\
            }\
        }\
        currentTest.code = code;\
              \
\
\
        iframe = document.createElement(\"iframe\");\
        iframe.setAttribute(\"id\", \"runnerIframe\");\
        //FireFox has a defect where it doesn't fire window.onerror for an iframe if the iframe\
        //is invisible.\
        if (!/firefox/i.test(navigator.userAgent)) {\
            iframe.setAttribute(\"style\", \"display:none\");\
        }\
        document.body.appendChild(iframe);\
\
        var iwin = window.frames[window.frames.length - 1];\
        var idoc = iwin.document;\
        idoc.open();\
\
        // Set up some globals.\
        iwin.testRun = testRun;\
        iwin.testFinished = testFinished;\
\
        //TODO: these should be moved to sta.js\
        var includes = code.match(/\\$INCLUDE\\(([^\\)]+)\\)/g), // find all of the $INCLUDE statements\
            include;\
\
        if (includes !== null) {\
            // We have some includes, so loop through each include and\
            // pull in the dependencies.\
            for (var i = 0; i < includes.length; i++) {\
                include = includes[i].replace(/.*\\(('|\")(.*)('|\")\\)/, \"$2\");\
\
                // First check to see if we have this script cached\
                // already, and if not, grab it.\
                if (typeof scriptCache[include] === \"undefined\") {\
                    $.ajax({\
                        async: false,\
                        url: 'harness/' + include,\
                        success: function (s) { scriptCache[include] = s; }\
                    });\
                }\
\
                // Finally, write the required script to the window.\
                idoc.writeln(\"<script type='text/javascript'>\" + scriptCache[include] + \"</script>\");\
            }\
        }\
\
        //Write out all of our helper functions\
        //idoc.writeln(\"<script type='text/javascript' src='harness/sta.js'>\" + \"</script>\");\
        idoc.writeln(\"<script type='text/javascript'>\");\
        idoc.writeln(simpleTestAPIContents);\
        idoc.writeln(\"</script>\");\
\
        iwin.iframeError = undefined;\
        iwin.onerror = undefined;\
        iwin.testDescrip = currentTest;\
\
        //Add an error handler capable of catching so-called early errors\
        //idoc.writeln(\"<script type='text/javascript' src='harness/ed.js'>\" + \"</script>\");\
        idoc.writeln(\"<script type='text/javascript'>\");\
        idoc.writeln(errorDetectorFileContents);\
        idoc.writeln(\"</script>\");\
\
        //Run the code\
        idoc.writeln(\"<script type='text/javascript'>\");\
        if (! instance.supportsWindowOnerror) {\
            idoc.writeln(\"try {eval(\\\"\" + this.convertForEval(code) + \"\\\");} catch(e) {window.onerror(e.toString(), null, null);}\");\
        } else {\
            idoc.writeln(code);\
        }\
        idoc.writeln(\"</script>\");\
\
        //Validate the results\
        //idoc.writeln(\"<script type='text/javascript' src='harness/gs.js' defer>\" + \"</script>\");\
        idoc.writeln(\"<script type='text/javascript'>\");\
        idoc.writeln(globalScopeContents);\
        idoc.writeln(\"</script>\");\
        idoc.close();\
        \
        var elapsed = new Date() - start;\
\
        return elapsed;\
    };\
\
    //--Helper functions-------------------------------------------------------\
    this.convertForEval = function(txt) {\
        txt = txt.replace(/\\\\/g,\"\\\\\\\\\");\
        txt = txt.replace(/\\\"/g,\"\\\\\\\"\");\
        txt = txt.replace(/\\'/g,\"\\\\\\'\");\
        txt = txt.replace(/\\r/g,\"\\\\r\");\
        txt = txt.replace(/\\n/g,\"\\\\n\");\
        return txt;\
    };\
}\
\
/* Loads tests from the sections specified in testcases.json.\
 * Public Methods:\
 * * getNextTest() - Start loading the next test.\
 * * reset() - Start over at the first test.\
 *\
 * Callbacks:\
 * * onLoadingNextSection(path): Called after a request is sent for the next section json, with the path to that json.\
 * * onInitialized(totalTests): Called after the testcases.json is loaded and parsed.\
 * * onTestReady(id, code): Called when a test is ready with the\
 *       test's id and code.\
 * * onTestsExhausted(): Called when there are no more tests to run.\
 */\
function TestLoader() {\
    var testGroups       = [],\
        testGroupIndex   = 0,\
        currentTestIndex = 0,\
        loader           = this,\
        mode             = \"all\";\
\
    this.loadedFiles = 0;\
    this.version     = undefined;\
    this.date        = undefined;\
    this.totalTests  = 0;\
    this.runningTests = 0;\
\
    /* Get the XML for the next section */\
    function getNextXML() {\
        currentTestIndex = 0;\
\
        // already loaded this section.\
        if(testGroups[testGroupIndex].status == 'loaded') {\
            testGroups[testGroupIndex].onLoaded = function(){};\
            loader.getNextTest();\
            return;\
        }\
        // not loaded, so we attach a callback to come back here when the file loads.\
        else {\
            presenter.updateStatus(\"Loading file: \" + testGroups[testGroupIndex].path);\
            testGroups[testGroupIndex].onLoaded = getNextXML;\
            \
        }\
    }\
    \
    /* Get the test list xml */\
    function loadTestXML() {\
        var testsListLoader = new XMLHttpRequest();\
\
        $.ajax({url: TEST_LIST_PATH, dataType: 'json', success: function(data) {\
            var testSuite = data.testSuite;\
\
            loader.version    = data.version;\
            loader.date       = data.date;\
            loader.totalTests = data.numTests;\
\
            for (var i = 0; i < testSuite.length; i++) {\
                testGroups[i] = {\
                    path: testSuite[i],\
                    tests: [],\
                    selected: false,\
                    status: 'waiting',\
                    onLoaded: function(){}\
                };\
                presenter.setTestWaiting(i, testSuite[i]);\
                \
                var tr = $('#chapterSelector table tr').filter(':nth-child(' + (i+1) + ')');\
                tr.find('img').filter('[alt=\"Run\"]').bind('click', {index:i}, function(event){\
                    controller.runIndividualTest(event.data.index);\
                });\
            }\
            loader.onInitialized(loader.totalTests);\
            getFile();\
        }});\
    }\
    \
    /* Get the test file. Handles all the logic of figuring out the next file to load. */\
    function getFile(index) {\
        index = (arguments.length == 0) ? -1 : index;\
        \
        // Look for selected waiting chapters (priority because you'll probably want to run them soon)\
        for(var i = 0; index == -1 && i < testGroups.length; i++) {\
            if(testGroups[i].status == 'waiting' && testGroups[i].selected) {\
                index = i;\
            }\
        }\
        \
        // Look for just chapters waiting to be loaded.\
        for(var i = 0; index == -1 && i < testGroups.length; i++) {\
            if(testGroups[i].status == 'waiting') {\
                index = i;\
            }\
        }\
            \
        if(index == -1) {\
            // Still -1? No more tests are waiting to be loaded then.\
            if(controller.state == 'loading') {\
                presenter.setState('loaded');\
            }\
            return;\
        }\
        \
        presenter.setTestLoading(index, testGroups[index].path);\
        // the only other status that should be set when we get here is 'priorityloading'\
        if(testGroups[index].status == 'waiting') {\
            testGroups[index].status = 'loading';\
        }\
        \
        loader.onTestStartLoading(index, testGroups[index].path);\
        // Create the AJAX call to grab the file.\
        $.ajax({\
            url: testGroups[index].path,\
            dataType: 'json',\
            // Callback with the chapter name and number of tests.\
            success: function(data, status, xhr) {\
                // Save the data for later usage\
                testGroups[index].tests = data.testsCollection.tests;\
                onTestLoaded(index, data.testsCollection.name, data.testsCollection.tests.length);\
            },\
            error: function(xhr, textStatus, errorThrown) {\
                // TODO: Catch this error and update UI accordingly. Unlikely to happen, but errors would be 404 or 5-- errors.\
                \
            }\
        });\
    }\
    \
    /* Executes when a test file finishes loading. */\
    function onTestLoaded(index, name, numTests) {\
        presenter.setTestLoaded(index, name, numTests);\
\
        if(testGroups[index].selected && mode == \"multiple\") {\
            loader.runningTests += numTests;\
            loader.onInitialized( loader.runningTests );\
        }\
        \
        // The loading status is only assigned when downloading files in sequence, otherwise it\
        // gets the status of priorityloading. When loading out of order, we only want to download\
        // the single file, so we'll only tell it to get the next file when we see a status of\
        // loading.\
        if(testGroups[index].status == 'loading') {\
            getFile(); // triggers downloading the next file\
            testGroups[index].status = 'loaded';\
        }\
        else if(testGroups[index].status == 'priorityloading') {\
            // Run the test\
            testGroups[index].status = 'loaded';\
            loader.setChapter(index);\
        }\
        \
        testGroups[index].onLoaded();\
    };\
    \
    function getIdFromPath (path) {\
        //path is of the form \"a/b/c.js\"\
\
        var id = path.split(\"/\");\
        //id is now of the form [\"a\", \"b\", \"c.js\"];\
\
        id = id[id.length-1];\
        //id is now of the form \"c.js\"\
\
        id = id.replace(/\\.js$/i, \"\");\
        //id is now of the form \"c\"\
\
        return id;\
    }\
\
    /* Move on to the next test */\
    this.getNextTest = function() {\
        // If the file is loaded\
        if(testGroups[testGroupIndex].status == \"loaded\")\
        {\
            // And if we have tests left in this file\
            if(currentTestIndex < testGroups[testGroupIndex].tests.length) {\
                // Run the next test\
                var test = testGroups[testGroupIndex].tests[currentTestIndex++];\
                var scriptCode = test.code;\
                test.id = getIdFromPath(test.path);\
\
                loader.onTestReady(test, $.base64Decode(scriptCode));\
            }\
            // If there are no tests left and we aren't just running one file\
            else if(testGroupIndex < testGroups.length - 1 && mode !== \"one\") {\
                // And if we are running multiple chapters\
                if(mode == \"multiple\") {\
                    var i = testGroupIndex + 1;\
                    testGroupIndex = -1;\
                    for(; i < testGroups.length && testGroupIndex == -1; i++) {\
                        if(testGroups[i].selected === true) {\
                            testGroupIndex = i;\
                        }\
                    }\
                    if(testGroupIndex == -1) { // we couldn't find a test we haven't run yet\
                        loader.onTestsExhausted();\
                        return;\
                    }\
                }\
                // And if \
                else {\
                    // We don't have tests left in this test group, so move on\
                    // to the next.\
                    testGroupIndex++;\
                }\
                getNextXML();\
            }\
            // \
            else {\
                // We're done.\
                loader.onTestsExhausted();\
            }\
        }\
        else {\
            presenter.updateStatus(\"Loading test file: \" + testGroups[testGroupIndex].path);\
            testGroups[testGroupIndex].onLoaded = getNextXML;\
        }\
    };\
\
    /* Reset counters that track the next test (so we test from the beginning) */\
    this.reset = function() {\
        mode = \"all\";\
        currentTestIndex = 0;\
        testGroupIndex = 0;\
    };\
    \
    /* Begin downloading test files. */\
    this.startLoadingTests = function() {\
        loadTestXML();\
    };\
    \
    /* Prepare for testing a single chapter. */\
    this.setChapter = function(index) {\
        currentTestIndex = 0;\
        testGroupIndex = index;\
        mode = \"one\";\
        \
        if(testGroups[index].status == 'loaded') {\
            loader.onInitialized(testGroups[index].tests.length);\
        }\
        else {\
            testGroups[index].status = 'priorityloading';\
            getFile(index);\
            loader.onInitialized(0);\
        }\
    };\
    \
    /* Prepare for testing multiple chapters. Returns true if at least one chapter was selected. */\
    this.setMultiple = function() {\
        // Find the index of the first selection\
        var firstSelectedIndex = -1;\
        for(var i = 0; firstSelectedIndex == -1 && i < testGroups.length; i++) {\
            if(testGroups[i].selected) {\
                firstSelectedIndex = i;\
            }\
        }\
        // If we didn't find a selected index, just quit.\
        if(firstSelectedIndex == -1) {\
            return false;\
        }\
        \
        // Begin loading the file immediately, if necessary\
        if(testGroups[firstSelectedIndex].status == 'waiting') {\
            getFile(firstSelectedIndex);\
        }\
    \
        mode = \"multiple\";\
        testGroupIndex = firstSelectedIndex; // start at this chapter\
        currentTestIndex = 0; // start at test 0\
        \
        // Count the number of tests\
        runningTests = 0;\
        for(var i = 0; i < testGroups.length; i++) {\
            runningTests += (testGroups[i].selected && testGroups[i].status == 'loaded') ? testGroups[i].tests.length : 0;\
        }\
        loader.onInitialized(runningTests);\
        return true;\
    };\
    \
    this.getNumTestFiles = function() {\
        return testGroups.length;\
    };\
    \
    /* Toggle the selection of a file. */\
    this.toggleSelection = function(index) {\
        testGroups[index].selected = !testGroups[index].selected;\
    }\
    \
}\
\
/* Controls test generation and running, and sends results to the presenter. */\
function Controller() {\
    var state  = 'undefined';\
    var runner = new BrowserRunner();\
    var loader = new TestLoader();\
    var controller = this;\
    var startTime;\
    var elapsed = 0;\
    //Hook which allows browser implementers to hook their own test harness API\
    //into this test framework to handle test case failures and passes in their\
    //own way (e.g., logging failures to the filesystem)\
    this.implementerHook = {\
        //Adds a test result\
        addTestResult: function (test) { },\
\
        //Called whenever all tests have finished running.  Provided with the\
        //elapsed time in milliseconds.\
        finished: function(elapsed) { }\
    };\
\
    /* Executes when a test case finishes executing. */\
    runner.onComplete = function(test) {\
        presenter.addTestResult(test);\
        try {\
            controller.implementerHook.addTestResult(test);\
        } catch(e) { /*no-op*/}\
\
        if(state === 'running') {\
            setTimeout(loader.getNextTest, 10);\
        }\
    };\
\
    /* Executes when the loader has been initialized. */\
    loader.onInitialized = function(totalTests) {\
        if(arguments.length == 0) {\
            totalTests = loader.totalTests;\
        }\
        presenter.setTotalTests(totalTests);\
    };\
    \
    /* Executes when a test file starts loading. */\
    loader.onTestStartLoading = function(index, path) {\
        presenter.setTestLoading(index, path);\
    }\
\
    /* Executes when a test is ready to run. */\
    loader.onTestReady = function(testObj, testSrc) {\
        presenter.updateStatus(\"Running Test: \" + testObj.id);\
        elapsed += runner.run(testObj, testSrc);\
    };\
\
    /* Executes when there are no more tests to run. */\
    loader.onTestsExhausted = function() {\
        elapsed = elapsed/(1000*60);  //minutes\
        elapsed = elapsed.toFixed(3);\
        \
        state = (loader.loadedFiles == loader.getNumTestFiles()) ? 'loaded' : 'loading';\
        presenter.setState(state);\
        presenter.finished(elapsed);\
        try {\
            controller.implementerHook.finished(elapsed);\
        } catch(e) { /*no-op*/}\
    };\
    \
    /* Start the test execution. */\
    this.start = function() {\
        elapsed = 0;\
        state = 'running';\
        presenter.setState(state);\
        loader.getNextTest();\
    };\
\
    /* Pause the test execution. */\
    this.pause = function() {\
        state = 'paused';\
        presenter.setState(state);\
    };\
\
    /* Reset the testing status. */\
    this.reset = function() {\
        loader.onInitialized();\
        loader.reset();\
        presenter.reset();\
        \
        state = (loader.loadedFiles == loader.getNumTestFiles()) ? 'loaded' : 'loading';\
        presenter.setState(state);\
    };\
    \
    /* Start loading tests. */\
    this.startLoadingTests = function() {\
        state = 'loading';\
        presenter.setState(state);\
        loader.startLoadingTests();\
    }\
    \
    /* Set the individual chapter in the laoder and start the controller. */\
    this.runIndividualTest = function(index) {\
        controller.reset();\
        loader.setChapter(index);\
        controller.start();\
    }\
    \
    /* Compile a list of the selected tests and start the controller. */\
    this.runSelected = function() {\
        controller.reset();\
        if(loader.setMultiple()) {\
            controller.start();\
        }\
    }\
    \
    this.runAll = function() {\
        controller.reset();\
        controller.start();\
    }\
    \
    this.toggleSelection = function(index) {\
        loader.toggleSelection(index);\
    }\
}\
\
var controller = new Controller();\
\
/* Helper function which shows if we're in the 'debug' mode of the Test262 site.\
   This mode is only useful for debugging issues with the test harness and\
   website. */\
function isSiteDebugMode() {\
    var str=window.location.href.substring(window.location.href.indexOf(\"?\")+1);\
    if(str.indexOf(\"sitedebug\") > -1) {\
        return true;\
    }\
    else {\
        return false;\
    }\
}\
\
\
$(function () {\
    presenter.setup();\
    $('.content-home').show();\
    // Adding attribute to the tabs (e.g. Home, Run etc.) and\
    // attaching the click event on buttons (e.g. Reset, Start etc.)\
    $('.nav-link').each(function (index) {\
        //Adding \"targetDiv\" attribute to the header tab and on that\
        //basis the div related to header tabs are displayed\
        if (index === 0) {\
            $(this).attr('targetDiv', '.content-home');\
        } else if (index === 1) {\
            $(this).attr('targetDiv', '.content-tests');\
        } else if (index === 2) {\
            $(this).attr('targetDiv', '.content-results');\
            $(this).attr('testRunning', 'false');\
        } else if (index === 3) {\
            $(this).attr('targetDiv', '.content-dev');\
        }\
        else {\
            $(this).attr('targetDiv', '.content-browsers');\
        }\
\
        //Attaching the click event to the header tab that shows the\
        //respective div of header\
        $(this).click(function () {\
            var target = $(this).attr('targetDiv');\
            $('#contentContainer > div:visible').hide();\
            $('.navBar .selected').toggleClass('selected');\
            $(this).addClass('selected');\
            $(target).show();\
\
            //If clicked tab is Result, it generates the results.\
            if ($(target).hasClass('content-results')) {\
                presenter.refresh();\
            }\
        });\
    });\
\
    // Attach click events to all the control buttons.\
    $('#btnRunAll').click(controller.runAll);\
    $('#btnReset').click(controller.reset);\
    $('#btnRunSelected').click(controller.runSelected);\
    $('#btnPause').click(controller.pause);\
    $('#btnResume').click(controller.start);\
\
    var SUITE_DESCRIP_PATH = \"json/suiteDescrip.json\";\
    $.ajax({ url: SUITE_DESCRIP_PATH, dataType: 'json', success: function (data) {\
        presenter.setVersion(data.version);\
        presenter.setDate(data.date);\
    }\
    });\
    \
    // Start loading the files right away.\
    controller.startLoadingTests();\
\
});\
";
t262Libs["testBuiltInObject.js"] = "// Copyright 2012 Mozilla Corporation. All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
/**\
 * @description Tests that obj meets the requirements for built-in objects\
 *     defined by the introduction of chapter 15 of the ECMAScript Language Specification.\
 * @param {Object} obj the object to be tested.\
 * @param {boolean} isFunction whether the specification describes obj as a function.\
 * @param {boolean} isConstructor whether the specification describes obj as a constructor.\
 * @param {String[]} properties an array with the names of the built-in properties of obj,\
 *     excluding length, prototype, or properties with non-default attributes.\
 * @param {number} length for functions only: the length specified for the function\
 *     or derived from the argument list.\
 * @author Norbert Lindenberg\
 */\
\
function testBuiltInObject(obj, isFunction, isConstructor, properties, length) {\
\
    if (obj === undefined) {\
        $ERROR(\"Object being tested is undefined.\");\
    }\
\
    var objString = Object.prototype.toString.call(obj);\
    if (isFunction) {\
        if (objString !== \"[object Function]\") {\
            $ERROR(\"The [[Class]] internal property of a built-in function must be \" +\
                    \"\\\"Function\\\", but toString() returns \" + objString);\
        }\
    } else {\
        if (objString !== \"[object Object]\") {\
            $ERROR(\"The [[Class]] internal property of a built-in non-function object must be \" +\
                    \"\\\"Object\\\", but toString() returns \" + objString);\
        }\
    }\
\
    if (!Object.isExtensible(obj)) {\
        $ERROR(\"Built-in objects must be extensible.\");\
    }\
\
    if (isFunction && Object.getPrototypeOf(obj) !== Function.prototype) {\
        $ERROR(\"Built-in functions must have Function.prototype as their prototype.\");\
    }\
\
    if (isConstructor && Object.getPrototypeOf(obj.prototype) !== Object.prototype) {\
        $ERROR(\"Built-in prototype objects must have Object.prototype as their prototype.\");\
    }\
\
    // verification of the absence of the [[Construct]] internal property has\
    // been moved to the end of the test\
    \
    // verification of the absence of the prototype property has\
    // been moved to the end of the test\
\
    if (isFunction) {\
        \
        if (typeof obj.length !== \"number\" || obj.length !== Math.floor(obj.length)) {\
            $ERROR(\"Built-in functions must have a length property with an integer value.\");\
        }\
    \
        if (obj.length !== length) {\
            $ERROR(\"Function's length property doesn't have specified value; expected \" +\
                length + \", got \" + obj.length + \".\");\
        }\
\
        var desc = Object.getOwnPropertyDescriptor(obj, \"length\");\
        if (desc.writable) {\
            $ERROR(\"The length property of a built-in function must not be writable.\");\
        }\
        if (desc.enumerable) {\
            $ERROR(\"The length property of a built-in function must not be enumerable.\");\
        }\
        if (desc.configurable) {\
            $ERROR(\"The length property of a built-in function must not be configurable.\");\
        }\
    }\
\
    properties.forEach(function(prop) {\
        var desc = Object.getOwnPropertyDescriptor(obj, prop);\
        if (desc === undefined) {\
            $ERROR(\"Missing property \" + prop + \".\");\
        }\
        // accessor properties don't have writable attribute\
        if (desc.hasOwnProperty(\"writable\") && !desc.writable) {\
            $ERROR(\"The \" + prop + \" property of this built-in function must be writable.\");\
        }\
        if (desc.enumerable) {\
            $ERROR(\"The \" + prop + \" property of this built-in function must not be enumerable.\");\
        }\
        if (!desc.configurable) {\
            $ERROR(\"The \" + prop + \" property of this built-in function must be configurable.\");\
        }\
    });\
\
    // The remaining sections have been moved to the end of the test because\
    // unbound non-constructor functions written in JavaScript cannot possibly\
    // pass them, and we still want to test JavaScript implementations as much\
    // as possible.\
    \
    var exception;\
    if (isFunction && !isConstructor) {\
        // this is not a complete test for the presence of [[Construct]]:\
        // if it's absent, the exception must be thrown, but it may also\
        // be thrown if it's present and just has preconditions related to\
        // arguments or the this value that this statement doesn't meet.\
        try {\
            /*jshint newcap:false*/\
            var instance = new obj();\
        } catch (e) {\
            exception = e;\
        }\
        if (exception === undefined || exception.name !== \"TypeError\") {\
            $ERROR(\"Built-in functions that aren't constructors must throw TypeError when \" +\
                \"used in a \\\"new\\\" statement.\");\
        }\
    }\
\
    if (isFunction && !isConstructor && obj.hasOwnProperty(\"prototype\")) {\
        $ERROR(\"Built-in functions that aren't constructors must not have a prototype property.\");\
    }\
\
    // passed the complete test!\
    return true;\
}\
\
";
t262Libs["testIntl.js"] = "// Copyright 2011-2012 Norbert Lindenberg. All rights reserved.\
// Copyright 2012-2013 Mozilla Corporation. All rights reserved.\
// This code is governed by the BSD license found in the LICENSE file.\
\
/**\
 * This file contains shared functions for the tests in the conformance test\
 * suite for the ECMAScript Internationalization API.\
 * @author Norbert Lindenberg\
 */\
\
\
/**\
 * @description Calls the provided function for every service constructor in\
 * the Intl object, until f returns a falsy value. It returns the result of the\
 * last call to f, mapped to a boolean.\
 * @param {Function} f the function to call for each service constructor in\
 *     the Intl object.\
 *     @param {Function} Constructor the constructor object to test with.\
 * @result {Boolean} whether the test succeeded.\
 */\
function testWithIntlConstructors(f) {\
    var constructors = [\"Collator\", \"NumberFormat\", \"DateTimeFormat\"];\
    return constructors.every(function (constructor) {\
        var Constructor = Intl[constructor];\
        var result;\
        try {\
            result = f(Constructor);\
        } catch (e) {\
            e.message += \" (Testing with \" + constructor + \".)\";\
            throw e;\
        }\
        return result;\
    });\
}\
\
\
/**\
 * Returns the name of the given constructor object, which must be one of\
 * Intl.Collator, Intl.NumberFormat, or Intl.DateTimeFormat.\
 * @param {object} Constructor a constructor\
 * @return {string} the name of the constructor\
 */\
function getConstructorName(Constructor) {\
    switch (Constructor) {\
        case Intl.Collator:\
            return \"Collator\";\
        case Intl.NumberFormat:\
            return \"NumberFormat\";\
        case Intl.DateTimeFormat:\
            return \"DateTimeFormat\";\
        default:\
            $ERROR(\"test internal error: unknown Constructor\");\
    }\
}\
\
\
/**\
 * Taints a named data property of the given object by installing\
 * a setter that throws an exception.\
 * @param {object} obj the object whose data property to taint\
 * @param {string} property the property to taint\
 */\
function taintDataProperty(obj, property) {\
    Object.defineProperty(obj, property, {\
        set: function(value) {\
            $ERROR(\"Client code can adversely affect behavior: setter for \" + property + \".\");\
        },\
        enumerable: false,\
        configurable: true\
    });\
}\
\
\
/**\
 * Taints a named method of the given object by replacing it with a function\
 * that throws an exception.\
 * @param {object} obj the object whose method to taint\
 * @param {string} property the name of the method to taint\
 */\
function taintMethod(obj, property) {\
    Object.defineProperty(obj, property, {\
        value: function() {\
            $ERROR(\"Client code can adversely affect behavior: method \" + property + \".\");\
        },\
        writable: true,\
        enumerable: false,\
        configurable: true\
    });\
}\
\
\
/**\
 * Taints the given properties (and similarly named properties) by installing\
 * setters on Object.prototype that throw exceptions.\
 * @param {Array} properties an array of property names to taint\
 */\
function taintProperties(properties) {\
    properties.forEach(function (property) {\
        var adaptedProperties = [property, \"__\" + property, \"_\" + property, property + \"_\", property + \"__\"];\
        adaptedProperties.forEach(function (property) {\
            taintDataProperty(Object.prototype, property);\
        });\
    });\
}\
\
\
/**\
 * Taints the Array object by creating a setter for the property \"0\" and\
 * replacing some key methods with functions that throw exceptions.\
 */\
function taintArray() {\
    taintDataProperty(Array.prototype, \"0\");\
    taintMethod(Array.prototype, \"indexOf\");\
    taintMethod(Array.prototype, \"join\");\
    taintMethod(Array.prototype, \"push\");\
    taintMethod(Array.prototype, \"slice\");\
    taintMethod(Array.prototype, \"sort\");\
}\
\
\
// auxiliary data for getLocaleSupportInfo\
var languages = [\"zh\", \"es\", \"en\", \"hi\", \"ur\", \"ar\", \"ja\", \"pa\"];\
var scripts = [\"Latn\", \"Hans\", \"Deva\", \"Arab\", \"Jpan\", \"Hant\"];\
var countries = [\"CN\", \"IN\", \"US\", \"PK\", \"JP\", \"TW\", \"HK\", \"SG\"];\
var localeSupportInfo = {};\
\
\
/**\
 * Gets locale support info for the given constructor object, which must be one\
 * of Intl.Collator, Intl.NumberFormat, Intl.DateTimeFormat.\
 * @param {object} Constructor the constructor for which to get locale support info\
 * @return {object} locale support info with the following properties:\
 *     supported: array of fully supported language tags\
 *     byFallback: array of language tags that are supported through fallbacks\
 *     unsupported: array of unsupported language tags\
 */\
function getLocaleSupportInfo(Constructor) {\
    var constructorName = getConstructorName(Constructor);\
    if (localeSupportInfo[constructorName] !== undefined) {\
        return localeSupportInfo[constructorName];\
    }\
\
    var allTags = [];\
    var i, j, k;\
    var language, script, country;\
    for (i = 0; i < languages.length; i++) {\
        language = languages[i];\
        allTags.push(language);\
        for (j = 0; j < scripts.length; j++) {\
            script = scripts[j];\
            allTags.push(language + \"-\" + script);\
            for (k = 0; k < countries.length; k++) {\
                country = countries[k];\
                allTags.push(language + \"-\" + script + \"-\" + country);\
            }\
        }\
        for (k = 0; k < countries.length; k++) {\
            country = countries[k];\
            allTags.push(language + \"-\" + country);\
        }\
    }\
    \
    var supported = [];\
    var byFallback = [];\
    var unsupported = [];\
    for (i = 0; i < allTags.length; i++) {\
        var request = allTags[i];\
        var result = new Constructor([request], {localeMatcher: \"lookup\"}).resolvedOptions().locale;\
         if (request === result) {\
            supported.push(request);\
        } else if (request.indexOf(result) === 0) {\
            byFallback.push(request);\
        } else {\
            unsupported.push(request);\
        }\
    }\
    \
    localeSupportInfo[constructorName] = {\
        supported: supported,\
        byFallback: byFallback,\
        unsupported: unsupported\
    };\
    \
    return localeSupportInfo[constructorName];\
}\
        \
\
/**\
 * @description Tests whether locale is a String value representing a\
 * structurally valid and canonicalized BCP 47 language tag, as defined in\
 * sections 6.2.2 and 6.2.3 of the ECMAScript Internationalization API\
 * Specification.\
 * @param {String} locale the string to be tested.\
 * @result {Boolean} whether the test succeeded.\
 */\
function isCanonicalizedStructurallyValidLanguageTag(locale) {\
\
    /**\
     * Regular expression defining BCP 47 language tags.\
     *\
     * Spec: RFC 5646 section 2.1.\
     */\
    var alpha = \"[a-zA-Z]\",\
        digit = \"[0-9]\",\
        alphanum = \"(\" + alpha + \"|\" + digit + \")\",\
        regular = \"(art-lojban|cel-gaulish|no-bok|no-nyn|zh-guoyu|zh-hakka|zh-min|zh-min-nan|zh-xiang)\",\
        irregular = \"(en-GB-oed|i-ami|i-bnn|i-default|i-enochian|i-hak|i-klingon|i-lux|i-mingo|i-navajo|i-pwn|i-tao|i-tay|i-tsu|sgn-BE-FR|sgn-BE-NL|sgn-CH-DE)\",\
        grandfathered = \"(\" + irregular + \"|\" + regular + \")\",\
        privateuse = \"(x(-[a-z0-9]{1,8})+)\",\
        singleton = \"(\" + digit + \"|[A-WY-Za-wy-z])\",\
        extension = \"(\" + singleton + \"(-\" + alphanum + \"{2,8})+)\",\
        variant = \"(\" + alphanum + \"{5,8}|(\" + digit + alphanum + \"{3}))\",\
        region = \"(\" + alpha + \"{2}|\" + digit + \"{3})\",\
        script = \"(\" + alpha + \"{4})\",\
        extlang = \"(\" + alpha + \"{3}(-\" + alpha + \"{3}){0,2})\",\
        language = \"(\" + alpha + \"{2,3}(-\" + extlang + \")?|\" + alpha + \"{4}|\" + alpha + \"{5,8})\",\
        langtag = language + \"(-\" + script + \")?(-\" + region + \")?(-\" + variant + \")*(-\" + extension + \")*(-\" + privateuse + \")?\",\
        languageTag = \"^(\" + langtag + \"|\" + privateuse + \"|\" + grandfathered + \")$\",\
        languageTagRE = new RegExp(languageTag, \"i\");\
    var duplicateSingleton = \"-\" + singleton + \"-(.*-)?\\\\1(?!\" + alphanum + \")\",\
        duplicateSingletonRE = new RegExp(duplicateSingleton, \"i\"),\
        duplicateVariant = \"(\" + alphanum + \"{2,8}-)+\" + variant + \"-(\" + alphanum + \"{2,8}-)*\\\\3(?!\" + alphanum + \")\",\
        duplicateVariantRE = new RegExp(duplicateVariant, \"i\");\
\
\
    /**\
     * Verifies that the given string is a well-formed BCP 47 language tag\
     * with no duplicate variant or singleton subtags.\
     *\
     * Spec: ECMAScript Internationalization API Specification, draft, 6.2.2.\
     */\
    function isStructurallyValidLanguageTag(locale) {\
        if (!languageTagRE.test(locale)) {\
            return false;\
        }\
        locale = locale.split(/-x-/)[0];\
        return !duplicateSingletonRE.test(locale) && !duplicateVariantRE.test(locale);\
    }\
\
\
    /**\
     * Mappings from complete tags to preferred values.\
     *\
     * Spec: IANA Language Subtag Registry.\
     */\
    var __tagMappings = {\
        // property names must be in lower case; values in canonical form\
\
        // grandfathered tags from IANA language subtag registry, file date 2011-08-25\
        \"art-lojban\": \"jbo\",\
        \"cel-gaulish\": \"cel-gaulish\",\
        \"en-gb-oed\": \"en-GB-oed\",\
        \"i-ami\": \"ami\",\
        \"i-bnn\": \"bnn\",\
        \"i-default\": \"i-default\",\
        \"i-enochian\": \"i-enochian\",\
        \"i-hak\": \"hak\",\
        \"i-klingon\": \"tlh\",\
        \"i-lux\": \"lb\",\
        \"i-mingo\": \"i-mingo\",\
        \"i-navajo\": \"nv\",\
        \"i-pwn\": \"pwn\",\
        \"i-tao\": \"tao\",\
        \"i-tay\": \"tay\",\
        \"i-tsu\": \"tsu\",\
        \"no-bok\": \"nb\",\
        \"no-nyn\": \"nn\",\
        \"sgn-be-fr\": \"sfb\",\
        \"sgn-be-nl\": \"vgt\",\
        \"sgn-ch-de\": \"sgg\",\
        \"zh-guoyu\": \"cmn\",\
        \"zh-hakka\": \"hak\",\
        \"zh-min\": \"zh-min\",\
        \"zh-min-nan\": \"nan\",\
        \"zh-xiang\": \"hsn\",\
        // deprecated redundant tags from IANA language subtag registry, file date 2011-08-25\
        \"sgn-br\": \"bzs\",\
        \"sgn-co\": \"csn\",\
        \"sgn-de\": \"gsg\",\
        \"sgn-dk\": \"dsl\",\
        \"sgn-es\": \"ssp\",\
        \"sgn-fr\": \"fsl\",\
        \"sgn-gb\": \"bfi\",\
        \"sgn-gr\": \"gss\",\
        \"sgn-ie\": \"isg\",\
        \"sgn-it\": \"ise\",\
        \"sgn-jp\": \"jsl\",\
        \"sgn-mx\": \"mfs\",\
        \"sgn-ni\": \"ncs\",\
        \"sgn-nl\": \"dse\",\
        \"sgn-no\": \"nsl\",\
        \"sgn-pt\": \"psr\",\
        \"sgn-se\": \"swl\",\
        \"sgn-us\": \"ase\",\
        \"sgn-za\": \"sfs\",\
        \"zh-cmn\": \"cmn\",\
        \"zh-cmn-hans\": \"cmn-Hans\",\
        \"zh-cmn-hant\": \"cmn-Hant\",\
        \"zh-gan\": \"gan\",\
        \"zh-wuu\": \"wuu\",\
        \"zh-yue\": \"yue\",\
        // deprecated variant with prefix from IANA language subtag registry, file date 2011-08-25\
        \"ja-latn-hepburn-heploc\": \"ja-Latn-alalc97\"\
    };\
\
\
    /**\
     * Mappings from non-extlang subtags to preferred values.\
     *\
     * Spec: IANA Language Subtag Registry.\
     */\
    var __subtagMappings = {\
        // property names and values must be in canonical case\
        // language subtags with Preferred-Value mappings from IANA language subtag registry, file date 2011-08-25\
        \"in\": \"id\",\
        \"iw\": \"he\",\
        \"ji\": \"yi\",\
        \"jw\": \"jv\",\
        \"mo\": \"ro\",\
        \"ayx\": \"nun\",\
        \"cjr\": \"mom\",\
        \"cmk\": \"xch\",\
        \"drh\": \"khk\",\
        \"drw\": \"prs\",\
        \"gav\": \"dev\",\
        \"mst\": \"mry\",\
        \"myt\": \"mry\",\
        \"tie\": \"ras\",\
        \"tkk\": \"twm\",\
        \"tnf\": \"prs\",\
        // region subtags with Preferred-Value mappings from IANA language subtag registry, file date 2011-08-25\
        \"BU\": \"MM\",\
        \"DD\": \"DE\",\
        \"FX\": \"FR\",\
        \"TP\": \"TL\",\
        \"YD\": \"YE\",\
        \"ZR\": \"CD\"\
    };\
\
\
    /**\
     * Mappings from extlang subtags to preferred values.\
     *\
     * Spec: IANA Language Subtag Registry.\
     */\
    var __extlangMappings = {\
        // extlang subtags with Preferred-Value mappings from IANA language subtag registry, file date 2011-08-25\
        // values are arrays with [0] the replacement value, [1] (if present) the prefix to be removed\
        \"aao\": [\"aao\", \"ar\"],\
        \"abh\": [\"abh\", \"ar\"],\
        \"abv\": [\"abv\", \"ar\"],\
        \"acm\": [\"acm\", \"ar\"],\
        \"acq\": [\"acq\", \"ar\"],\
        \"acw\": [\"acw\", \"ar\"],\
        \"acx\": [\"acx\", \"ar\"],\
        \"acy\": [\"acy\", \"ar\"],\
        \"adf\": [\"adf\", \"ar\"],\
        \"ads\": [\"ads\", \"sgn\"],\
        \"aeb\": [\"aeb\", \"ar\"],\
        \"aec\": [\"aec\", \"ar\"],\
        \"aed\": [\"aed\", \"sgn\"],\
        \"aen\": [\"aen\", \"sgn\"],\
        \"afb\": [\"afb\", \"ar\"],\
        \"afg\": [\"afg\", \"sgn\"],\
        \"ajp\": [\"ajp\", \"ar\"],\
        \"apc\": [\"apc\", \"ar\"],\
        \"apd\": [\"apd\", \"ar\"],\
        \"arb\": [\"arb\", \"ar\"],\
        \"arq\": [\"arq\", \"ar\"],\
        \"ars\": [\"ars\", \"ar\"],\
        \"ary\": [\"ary\", \"ar\"],\
        \"arz\": [\"arz\", \"ar\"],\
        \"ase\": [\"ase\", \"sgn\"],\
        \"asf\": [\"asf\", \"sgn\"],\
        \"asp\": [\"asp\", \"sgn\"],\
        \"asq\": [\"asq\", \"sgn\"],\
        \"asw\": [\"asw\", \"sgn\"],\
        \"auz\": [\"auz\", \"ar\"],\
        \"avl\": [\"avl\", \"ar\"],\
        \"ayh\": [\"ayh\", \"ar\"],\
        \"ayl\": [\"ayl\", \"ar\"],\
        \"ayn\": [\"ayn\", \"ar\"],\
        \"ayp\": [\"ayp\", \"ar\"],\
        \"bbz\": [\"bbz\", \"ar\"],\
        \"bfi\": [\"bfi\", \"sgn\"],\
        \"bfk\": [\"bfk\", \"sgn\"],\
        \"bjn\": [\"bjn\", \"ms\"],\
        \"bog\": [\"bog\", \"sgn\"],\
        \"bqn\": [\"bqn\", \"sgn\"],\
        \"bqy\": [\"bqy\", \"sgn\"],\
        \"btj\": [\"btj\", \"ms\"],\
        \"bve\": [\"bve\", \"ms\"],\
        \"bvl\": [\"bvl\", \"sgn\"],\
        \"bvu\": [\"bvu\", \"ms\"],\
        \"bzs\": [\"bzs\", \"sgn\"],\
        \"cdo\": [\"cdo\", \"zh\"],\
        \"cds\": [\"cds\", \"sgn\"],\
        \"cjy\": [\"cjy\", \"zh\"],\
        \"cmn\": [\"cmn\", \"zh\"],\
        \"coa\": [\"coa\", \"ms\"],\
        \"cpx\": [\"cpx\", \"zh\"],\
        \"csc\": [\"csc\", \"sgn\"],\
        \"csd\": [\"csd\", \"sgn\"],\
        \"cse\": [\"cse\", \"sgn\"],\
        \"csf\": [\"csf\", \"sgn\"],\
        \"csg\": [\"csg\", \"sgn\"],\
        \"csl\": [\"csl\", \"sgn\"],\
        \"csn\": [\"csn\", \"sgn\"],\
        \"csq\": [\"csq\", \"sgn\"],\
        \"csr\": [\"csr\", \"sgn\"],\
        \"czh\": [\"czh\", \"zh\"],\
        \"czo\": [\"czo\", \"zh\"],\
        \"doq\": [\"doq\", \"sgn\"],\
        \"dse\": [\"dse\", \"sgn\"],\
        \"dsl\": [\"dsl\", \"sgn\"],\
        \"dup\": [\"dup\", \"ms\"],\
        \"ecs\": [\"ecs\", \"sgn\"],\
        \"esl\": [\"esl\", \"sgn\"],\
        \"esn\": [\"esn\", \"sgn\"],\
        \"eso\": [\"eso\", \"sgn\"],\
        \"eth\": [\"eth\", \"sgn\"],\
        \"fcs\": [\"fcs\", \"sgn\"],\
        \"fse\": [\"fse\", \"sgn\"],\
        \"fsl\": [\"fsl\", \"sgn\"],\
        \"fss\": [\"fss\", \"sgn\"],\
        \"gan\": [\"gan\", \"zh\"],\
        \"gom\": [\"gom\", \"kok\"],\
        \"gse\": [\"gse\", \"sgn\"],\
        \"gsg\": [\"gsg\", \"sgn\"],\
        \"gsm\": [\"gsm\", \"sgn\"],\
        \"gss\": [\"gss\", \"sgn\"],\
        \"gus\": [\"gus\", \"sgn\"],\
        \"hab\": [\"hab\", \"sgn\"],\
        \"haf\": [\"haf\", \"sgn\"],\
        \"hak\": [\"hak\", \"zh\"],\
        \"hds\": [\"hds\", \"sgn\"],\
        \"hji\": [\"hji\", \"ms\"],\
        \"hks\": [\"hks\", \"sgn\"],\
        \"hos\": [\"hos\", \"sgn\"],\
        \"hps\": [\"hps\", \"sgn\"],\
        \"hsh\": [\"hsh\", \"sgn\"],\
        \"hsl\": [\"hsl\", \"sgn\"],\
        \"hsn\": [\"hsn\", \"zh\"],\
        \"icl\": [\"icl\", \"sgn\"],\
        \"ils\": [\"ils\", \"sgn\"],\
        \"inl\": [\"inl\", \"sgn\"],\
        \"ins\": [\"ins\", \"sgn\"],\
        \"ise\": [\"ise\", \"sgn\"],\
        \"isg\": [\"isg\", \"sgn\"],\
        \"isr\": [\"isr\", \"sgn\"],\
        \"jak\": [\"jak\", \"ms\"],\
        \"jax\": [\"jax\", \"ms\"],\
        \"jcs\": [\"jcs\", \"sgn\"],\
        \"jhs\": [\"jhs\", \"sgn\"],\
        \"jls\": [\"jls\", \"sgn\"],\
        \"jos\": [\"jos\", \"sgn\"],\
        \"jsl\": [\"jsl\", \"sgn\"],\
        \"jus\": [\"jus\", \"sgn\"],\
        \"kgi\": [\"kgi\", \"sgn\"],\
        \"knn\": [\"knn\", \"kok\"],\
        \"kvb\": [\"kvb\", \"ms\"],\
        \"kvk\": [\"kvk\", \"sgn\"],\
        \"kvr\": [\"kvr\", \"ms\"],\
        \"kxd\": [\"kxd\", \"ms\"],\
        \"lbs\": [\"lbs\", \"sgn\"],\
        \"lce\": [\"lce\", \"ms\"],\
        \"lcf\": [\"lcf\", \"ms\"],\
        \"liw\": [\"liw\", \"ms\"],\
        \"lls\": [\"lls\", \"sgn\"],\
        \"lsg\": [\"lsg\", \"sgn\"],\
        \"lsl\": [\"lsl\", \"sgn\"],\
        \"lso\": [\"lso\", \"sgn\"],\
        \"lsp\": [\"lsp\", \"sgn\"],\
        \"lst\": [\"lst\", \"sgn\"],\
        \"lsy\": [\"lsy\", \"sgn\"],\
        \"ltg\": [\"ltg\", \"lv\"],\
        \"lvs\": [\"lvs\", \"lv\"],\
        \"lzh\": [\"lzh\", \"zh\"],\
        \"max\": [\"max\", \"ms\"],\
        \"mdl\": [\"mdl\", \"sgn\"],\
        \"meo\": [\"meo\", \"ms\"],\
        \"mfa\": [\"mfa\", \"ms\"],\
        \"mfb\": [\"mfb\", \"ms\"],\
        \"mfs\": [\"mfs\", \"sgn\"],\
        \"min\": [\"min\", \"ms\"],\
        \"mnp\": [\"mnp\", \"zh\"],\
        \"mqg\": [\"mqg\", \"ms\"],\
        \"mre\": [\"mre\", \"sgn\"],\
        \"msd\": [\"msd\", \"sgn\"],\
        \"msi\": [\"msi\", \"ms\"],\
        \"msr\": [\"msr\", \"sgn\"],\
        \"mui\": [\"mui\", \"ms\"],\
        \"mzc\": [\"mzc\", \"sgn\"],\
        \"mzg\": [\"mzg\", \"sgn\"],\
        \"mzy\": [\"mzy\", \"sgn\"],\
        \"nan\": [\"nan\", \"zh\"],\
        \"nbs\": [\"nbs\", \"sgn\"],\
        \"ncs\": [\"ncs\", \"sgn\"],\
        \"nsi\": [\"nsi\", \"sgn\"],\
        \"nsl\": [\"nsl\", \"sgn\"],\
        \"nsp\": [\"nsp\", \"sgn\"],\
        \"nsr\": [\"nsr\", \"sgn\"],\
        \"nzs\": [\"nzs\", \"sgn\"],\
        \"okl\": [\"okl\", \"sgn\"],\
        \"orn\": [\"orn\", \"ms\"],\
        \"ors\": [\"ors\", \"ms\"],\
        \"pel\": [\"pel\", \"ms\"],\
        \"pga\": [\"pga\", \"ar\"],\
        \"pks\": [\"pks\", \"sgn\"],\
        \"prl\": [\"prl\", \"sgn\"],\
        \"prz\": [\"prz\", \"sgn\"],\
        \"psc\": [\"psc\", \"sgn\"],\
        \"psd\": [\"psd\", \"sgn\"],\
        \"pse\": [\"pse\", \"ms\"],\
        \"psg\": [\"psg\", \"sgn\"],\
        \"psl\": [\"psl\", \"sgn\"],\
        \"pso\": [\"pso\", \"sgn\"],\
        \"psp\": [\"psp\", \"sgn\"],\
        \"psr\": [\"psr\", \"sgn\"],\
        \"pys\": [\"pys\", \"sgn\"],\
        \"rms\": [\"rms\", \"sgn\"],\
        \"rsi\": [\"rsi\", \"sgn\"],\
        \"rsl\": [\"rsl\", \"sgn\"],\
        \"sdl\": [\"sdl\", \"sgn\"],\
        \"sfb\": [\"sfb\", \"sgn\"],\
        \"sfs\": [\"sfs\", \"sgn\"],\
        \"sgg\": [\"sgg\", \"sgn\"],\
        \"sgx\": [\"sgx\", \"sgn\"],\
        \"shu\": [\"shu\", \"ar\"],\
        \"slf\": [\"slf\", \"sgn\"],\
        \"sls\": [\"sls\", \"sgn\"],\
        \"sqs\": [\"sqs\", \"sgn\"],\
        \"ssh\": [\"ssh\", \"ar\"],\
        \"ssp\": [\"ssp\", \"sgn\"],\
        \"ssr\": [\"ssr\", \"sgn\"],\
        \"svk\": [\"svk\", \"sgn\"],\
        \"swc\": [\"swc\", \"sw\"],\
        \"swh\": [\"swh\", \"sw\"],\
        \"swl\": [\"swl\", \"sgn\"],\
        \"syy\": [\"syy\", \"sgn\"],\
        \"tmw\": [\"tmw\", \"ms\"],\
        \"tse\": [\"tse\", \"sgn\"],\
        \"tsm\": [\"tsm\", \"sgn\"],\
        \"tsq\": [\"tsq\", \"sgn\"],\
        \"tss\": [\"tss\", \"sgn\"],\
        \"tsy\": [\"tsy\", \"sgn\"],\
        \"tza\": [\"tza\", \"sgn\"],\
        \"ugn\": [\"ugn\", \"sgn\"],\
        \"ugy\": [\"ugy\", \"sgn\"],\
        \"ukl\": [\"ukl\", \"sgn\"],\
        \"uks\": [\"uks\", \"sgn\"],\
        \"urk\": [\"urk\", \"ms\"],\
        \"uzn\": [\"uzn\", \"uz\"],\
        \"uzs\": [\"uzs\", \"uz\"],\
        \"vgt\": [\"vgt\", \"sgn\"],\
        \"vkk\": [\"vkk\", \"ms\"],\
        \"vkt\": [\"vkt\", \"ms\"],\
        \"vsi\": [\"vsi\", \"sgn\"],\
        \"vsl\": [\"vsl\", \"sgn\"],\
        \"vsv\": [\"vsv\", \"sgn\"],\
        \"wuu\": [\"wuu\", \"zh\"],\
        \"xki\": [\"xki\", \"sgn\"],\
        \"xml\": [\"xml\", \"sgn\"],\
        \"xmm\": [\"xmm\", \"ms\"],\
        \"xms\": [\"xms\", \"sgn\"],\
        \"yds\": [\"yds\", \"sgn\"],\
        \"ysl\": [\"ysl\", \"sgn\"],\
        \"yue\": [\"yue\", \"zh\"],\
        \"zib\": [\"zib\", \"sgn\"],\
        \"zlm\": [\"zlm\", \"ms\"],\
        \"zmi\": [\"zmi\", \"ms\"],\
        \"zsl\": [\"zsl\", \"sgn\"],\
        \"zsm\": [\"zsm\", \"ms\"]\
    };\
\
\
    /**\
     * Canonicalizes the given well-formed BCP 47 language tag, including regularized case of subtags.\
     *\
     * Spec: ECMAScript Internationalization API Specification, draft, 6.2.3.\
     * Spec: RFC 5646, section 4.5.\
     */\
    function canonicalizeLanguageTag(locale) {\
\
        // start with lower case for easier processing, and because most subtags will need to be lower case anyway\
        locale = locale.toLowerCase();\
\
        // handle mappings for complete tags\
        if (__tagMappings.hasOwnProperty(locale)) {\
            return __tagMappings[locale];\
        }\
\
        var subtags = locale.split(\"-\");\
        var i = 0;\
\
        // handle standard part: all subtags before first singleton or \"x\"\
        while (i < subtags.length) {\
            var subtag = subtags[i];\
            if (subtag.length === 1 && (i > 0 || subtag === \"x\")) {\
                break;\
            } else if (i !== 0 && subtag.length === 2) {\
                subtag = subtag.toUpperCase();\
            } else if (subtag.length === 4) {\
                subtag = subtag[0].toUpperCase() + subtag.substring(1).toLowerCase();\
            }\
            if (__subtagMappings.hasOwnProperty(subtag)) {\
                subtag = __subtagMappings[subtag];\
            } else if (__extlangMappings.hasOwnProperty(subtag)) {\
                subtag = __extlangMappings[subtag][0];\
                if (i === 1 && __extlangMappings[subtag][1] === subtags[0]) {\
                    subtags.shift();\
                    i--;\
                }\
            }\
            subtags[i] = subtag;\
            i++;\
        }\
        var normal = subtags.slice(0, i).join(\"-\");\
\
        // handle extensions\
        var extensions = [];\
        while (i < subtags.length && subtags[i] !== \"x\") {\
            var extensionStart = i;\
            i++;\
            while (i < subtags.length && subtags[i].length > 1) {\
                i++;\
            }\
            var extension = subtags.slice(extensionStart, i).join(\"-\");\
            extensions.push(extension);\
        }\
        extensions.sort();\
\
        // handle private use\
        var privateUse;\
        if (i < subtags.length) {\
            privateUse = subtags.slice(i).join(\"-\");\
        }\
\
        // put everything back together\
        var canonical = normal;\
        if (extensions.length > 0) {\
            canonical += \"-\" + extensions.join(\"-\");\
        }\
        if (privateUse !== undefined) {\
            if (canonical.length > 0) {\
                canonical += \"-\" + privateUse;\
            } else {\
                canonical = privateUse;\
            }\
        }\
\
        return canonical;\
    }\
\
    return typeof locale === \"string\" && isStructurallyValidLanguageTag(locale) &&\
            canonicalizeLanguageTag(locale) === locale;\
}\
\
\
/**\
 * Tests whether the named options property is correctly handled by the given constructor.\
 * @param {object} Constructor the constructor to test.\
 * @param {string} property the name of the options property to test.\
 * @param {string} type the type that values of the property are expected to have\
 * @param {Array} [values] an array of allowed values for the property. Not needed for boolean.\
 * @param {any} fallback the fallback value that the property assumes if not provided.\
 * @param {object} testOptions additional options:\
 *     @param {boolean} isOptional whether support for this property is optional for implementations.\
 *     @param {boolean} noReturn whether the resulting value of the property is not returned.\
 *     @param {boolean} isILD whether the resulting value of the property is implementation and locale dependent.\
 *     @param {object} extra additional option to pass along, properties are value -> {option: value}.\
 * @return {boolean} whether the test succeeded.\
 */\
function testOption(Constructor, property, type, values, fallback, testOptions) {\
    var isOptional = testOptions !== undefined && testOptions.isOptional === true;\
    var noReturn = testOptions !== undefined && testOptions.noReturn === true;\
    var isILD = testOptions !== undefined && testOptions.isILD === true;\
    \
    function addExtraOptions(options, value, testOptions) {\
        if (testOptions !== undefined && testOptions.extra !== undefined) {\
            var extra;\
            if (value !== undefined && testOptions.extra[value] !== undefined) {\
                extra = testOptions.extra[value];\
            } else if (testOptions.extra.any !== undefined) {\
                extra = testOptions.extra.any;\
            }\
            if (extra !== undefined) {\
                Object.getOwnPropertyNames(extra).forEach(function (prop) {\
                    options[prop] = extra[prop];\
                });\
            }\
        }\
    }\
\
    var testValues, options, obj, expected, actual, error;\
\
    // test that the specified values are accepted. Also add values that convert to specified values.\
    if (type === \"boolean\") {\
        if (values === undefined) {\
            values = [true, false];\
        }\
        testValues = values.slice(0);\
        testValues.push(888);\
        testValues.push(0);\
    } else if (type === \"string\") {\
        testValues = values.slice(0);\
        testValues.push({toString: function () { return values[0]; }});\
    }\
    testValues.forEach(function (value) {\
        options = {};\
        options[property] = value;\
        addExtraOptions(options, value, testOptions);\
        obj = new Constructor(undefined, options);\
        if (noReturn) {\
            if (obj.resolvedOptions().hasOwnProperty(property)) {\
                $ERROR(\"Option property \" + property + \" is returned, but shouldn't be.\");\
            }\
        } else {\
            actual = obj.resolvedOptions()[property];\
            if (isILD) {\
                if (actual !== undefined && values.indexOf(actual) === -1) {\
                    $ERROR(\"Invalid value \" + actual + \" returned for property \" + property + \".\");\
                }\
            } else {\
                if (type === \"boolean\") {\
                    expected = Boolean(value);\
                } else if (type === \"string\") {\
                    expected = String(value);\
                }\
                if (actual !== expected && !(isOptional && actual === undefined)) {\
                    $ERROR(\"Option value \" + value + \" for property \" + property +\
                        \" was not accepted; got \" + actual + \" instead.\");\
                }\
            }\
        }\
    });\
\
    // test that invalid values are rejected\
    if (type === \"string\") {\
        var invalidValues = [\"invalidValue\", -1, null];\
        // assume that we won't have values in caseless scripts\
        if (values[0].toUpperCase() !== values[0]) {\
            invalidValues.push(values[0].toUpperCase());\
        } else {\
            invalidValues.push(values[0].toLowerCase());\
        }\
        invalidValues.forEach(function (value) {\
            options = {};\
            options[property] = value;\
            addExtraOptions(options, value, testOptions);\
            error = undefined;\
            try {\
                obj = new Constructor(undefined, options);\
            } catch (e) {\
                error = e;\
            }\
            if (error === undefined) {\
                $ERROR(\"Invalid option value \" + value + \" for property \" + property + \" was not rejected.\");\
            } else if (error.name !== \"RangeError\") {\
                $ERROR(\"Invalid option value \" + value + \" for property \" + property + \" was rejected with wrong error \" + error.name + \".\");\
            }\
        });\
    }\
\
    // test that fallback value or another valid value is used if no options value is provided\
    if (!noReturn) {\
        options = {};\
        addExtraOptions(options, undefined, testOptions);\
        obj = new Constructor(undefined, options);\
        actual = obj.resolvedOptions()[property];\
        if (!(isOptional && actual === undefined)) {\
            if (fallback !== undefined) {\
                if (actual !== fallback) {\
                    $ERROR(\"Option fallback value \" + fallback + \" for property \" + property +\
                        \" was not used; got \" + actual + \" instead.\");\
                }\
            } else {\
                if (values.indexOf(actual) === -1 && !(isILD && actual === undefined)) {\
                    $ERROR(\"Invalid value \" + actual + \" returned for property \" + property + \".\");\
                }\
            }\
        }\
    }\
\
    return true;\
}\
\
\
/**\
 * Tests whether the named property of the given object has a valid value\
 * and the default attributes of the properties of an object literal.\
 * @param {Object} obj the object to be tested.\
 * @param {string} property the name of the property\
 * @param {Function|Array} valid either a function that tests value for validity and returns a boolean,\
 *     an array of valid values.\
 * @exception if the property has an invalid value.\
 */\
function testProperty(obj, property, valid) {\
    var desc = Object.getOwnPropertyDescriptor(obj, property);\
    if (!desc.writable) {\
        $ERROR(\"Property \" + property + \" must be writable.\");\
    }\
    if (!desc.enumerable) {\
        $ERROR(\"Property \" + property + \" must be enumerable.\");\
    }\
    if (!desc.configurable) {\
        $ERROR(\"Property \" + property + \" must be configurable.\");\
    }\
    var value = desc.value;\
    var isValid = (typeof valid === \"function\") ? valid(value) : (valid.indexOf(value) !== -1);\
    if (!isValid) {\
        $ERROR(\"Property value \" + value + \" is not allowed for property \" + property + \".\");\
    }\
}\
\
\
/**\
 * Tests whether the named property of the given object, if present at all, has a valid value\
 * and the default attributes of the properties of an object literal.\
 * @param {Object} obj the object to be tested.\
 * @param {string} property the name of the property\
 * @param {Function|Array} valid either a function that tests value for validity and returns a boolean,\
 *     an array of valid values.\
 * @exception if the property is present and has an invalid value.\
 */\
function mayHaveProperty(obj, property, valid) {\
    if (obj.hasOwnProperty(property)) {\
        testProperty(obj, property, valid);\
    }\
}\
\
\
/**\
 * Tests whether the given object has the named property with a valid value\
 * and the default attributes of the properties of an object literal.\
 * @param {Object} obj the object to be tested.\
 * @param {string} property the name of the property\
 * @param {Function|Array} valid either a function that tests value for validity and returns a boolean,\
 *     an array of valid values.\
 * @exception if the property is missing or has an invalid value.\
 */\
function mustHaveProperty(obj, property, valid) {\
    if (!obj.hasOwnProperty(property)) {\
        $ERROR(\"Object is missing property \" + property + \".\");\
    }\
    testProperty(obj, property, valid);\
}\
\
\
/**\
 * Tests whether the given object does not have the named property.\
 * @param {Object} obj the object to be tested.\
 * @param {string} property the name of the property\
 * @exception if the property is present.\
 */\
function mustNotHaveProperty(obj, property) {\
    if (obj.hasOwnProperty(property)) {\
        $ERROR(\"Object has property it mustn't have: \" + property + \".\");\
    }\
}\
\
\
/**\
 * Properties of the RegExp constructor that may be affected by use of regular\
 * expressions, and the default values of these properties. Properties are from\
 * https://developer.mozilla.org/en-US/docs/JavaScript/Reference/Deprecated_and_obsolete_features#RegExp_Properties\
 */\
var regExpProperties = [\"$1\", \"$2\", \"$3\", \"$4\", \"$5\", \"$6\", \"$7\", \"$8\", \"$9\",\
    \"$_\", \"$*\", \"$&\", \"$+\", \"$`\", \"$'\",\
    \"input\", \"lastMatch\", \"lastParen\", \"leftContext\", \"rightContext\"\
];\
\
var regExpPropertiesDefaultValues = (function () {\
    var values = Object.create(null);\
    regExpProperties.forEach(function (property) {\
        values[property] = RegExp[property];\
    });\
    return values;\
}());\
\
\
/**\
 * Tests that executing the provided function (which may use regular expressions\
 * in its implementation) does not create or modify unwanted properties on the\
 * RegExp constructor.\
 */\
function testForUnwantedRegExpChanges(testFunc) {\
    regExpProperties.forEach(function (property) {\
        RegExp[property] = regExpPropertiesDefaultValues[property];\
    });\
    testFunc();\
    regExpProperties.forEach(function (property) {\
        if (RegExp[property] !== regExpPropertiesDefaultValues[property]) {\
            $ERROR(\"RegExp has unexpected property \" + property + \" with value \" +\
                RegExp[property] + \".\");\
        }\
    });\
}\
\
\
/**\
 * Tests whether name is a valid BCP 47 numbering system name\
 * and not excluded from use in the ECMAScript Internationalization API.\
 * @param {string} name the name to be tested.\
 * @return {boolean} whether name is a valid BCP 47 numbering system name and\
 *     allowed for use in the ECMAScript Internationalization API.\
 */\
\
function isValidNumberingSystem(name) {\
    \
    // source: CLDR file common/bcp47/number.xml; version CLDR 21.\
    var numberingSystems = [\
        \"arab\",\
        \"arabext\",\
        \"armn\",\
        \"armnlow\",\
        \"bali\",\
        \"beng\",\
        \"brah\",\
        \"cakm\",\
        \"cham\",\
        \"deva\",\
        \"ethi\",\
        \"finance\",\
        \"fullwide\",\
        \"geor\",\
        \"grek\",\
        \"greklow\",\
        \"gujr\",\
        \"guru\",\
        \"hanidec\",\
        \"hans\",\
        \"hansfin\",\
        \"hant\",\
        \"hantfin\",\
        \"hebr\",\
        \"java\",\
        \"jpan\",\
        \"jpanfin\",\
        \"kali\",\
        \"khmr\",\
        \"knda\",\
        \"osma\",            \
        \"lana\",\
        \"lanatham\",\
        \"laoo\",\
        \"latn\",\
        \"lepc\",\
        \"limb\",\
        \"mlym\",\
        \"mong\",\
        \"mtei\",\
        \"mymr\",\
        \"mymrshan\",\
        \"native\",\
        \"nkoo\",\
        \"olck\",\
        \"orya\",\
        \"roman\",\
        \"romanlow\",\
        \"saur\",\
        \"shrd\",\
        \"sora\",\
        \"sund\",\
        \"talu\",\
        \"takr\",\
        \"taml\",\
        \"tamldec\",\
        \"telu\",\
        \"thai\",\
        \"tibt\",\
        \"traditio\",\
        \"vaii\"\
    ];\
    \
    var excluded = [\
        \"finance\",\
        \"native\",\
        \"traditio\"\
    ];\
        \
    \
    return numberingSystems.indexOf(name) !== -1 && excluded.indexOf(name) === -1;\
}\
\
\
/**\
 * Provides the digits of numbering systems with simple digit mappings,\
 * as specified in 11.3.2.\
 */\
\
var numberingSystemDigits = {\
    arab: \"٠١٢٣٤٥٦٧٨٩\",\
    arabext: \"۰۱۲۳۴۵۶۷۸۹\",\
    beng: \"০১২৩৪৫৬৭৮৯\",\
    deva: \"०१२३४५६७८९\",\
    fullwide: \"０１２３４５６７８９\",\
    gujr: \"૦૧૨૩૪૫૬૭૮૯\",\
    guru: \"੦੧੨੩੪੫੬੭੮੯\",\
    hanidec: \"〇一二三四五六七八九\",\
    khmr: \"០១២៣៤៥៦៧៨៩\",\
    knda: \"೦೧೨೩೪೫೬೭೮೯\",\
    laoo: \"໐໑໒໓໔໕໖໗໘໙\",\
    latn: \"0123456789\",\
    mlym: \"൦൧൨൩൪൫൬൭൮൯\",\
    mong: \"᠐᠑᠒᠓᠔᠕᠖᠗᠘᠙\",\
    mymr: \"၀၁၂၃၄၅၆၇၈၉\",\
    orya: \"୦୧୨୩୪୫୬୭୮୯\",\
    tamldec: \"௦௧௨௩௪௫௬௭௮௯\",\
    telu: \"౦౧౨౩౪౫౬౭౮౯\",\
    thai: \"๐๑๒๓๔๕๖๗๘๙\",\
    tibt: \"༠༡༢༣༤༥༦༧༨༩\"\
};\
\
\
/**\
 * Tests that number formatting is handled correctly. The function checks that the\
 * digit sequences in formatted output are as specified, converted to the\
 * selected numbering system, and embedded in consistent localized patterns.\
 * @param {Array} locales the locales to be tested.\
 * @param {Array} numberingSystems the numbering systems to be tested.\
 * @param {Object} options the options to pass to Intl.NumberFormat. Options\
 *     must include {useGrouping: false}, and must cause 1.1 to be formatted\
 *     pre- and post-decimal digits.\
 * @param {Object} testData maps input data (in ES5 9.3.1 format) to expected output strings\
 *     in unlocalized format with Western digits.\
 */\
\
function testNumberFormat(locales, numberingSystems, options, testData) {\
    locales.forEach(function (locale) {\
        numberingSystems.forEach(function (numbering) {\
            var digits = numberingSystemDigits[numbering];\
            var format = new Intl.NumberFormat([locale + \"-u-nu-\" + numbering], options);\
    \
            function getPatternParts(positive) {\
                var n = positive ? 1.1 : -1.1;\
                var formatted = format.format(n);\
                var oneoneRE = \"([^\" + digits + \"]*)[\" + digits + \"]+([^\" + digits + \"]+)[\" + digits + \"]+([^\" + digits + \"]*)\";\
                var match = formatted.match(new RegExp(oneoneRE));\
                if (match === null) {\
                    $ERROR(\"Unexpected formatted \" + n + \" for \" +\
                        format.resolvedOptions().locale + \" and options \" +\
                        JSON.stringify(options) + \": \" + formatted);\
                }\
                return match;\
            }\
            \
            function toNumbering(raw) {\
                return raw.replace(/[0-9]/g, function (digit) {\
                    return digits[digit.charCodeAt(0) - \"0\".charCodeAt(0)];\
                });\
            }\
            \
            function buildExpected(raw, patternParts) {\
                var period = raw.indexOf(\".\");\
                if (period === -1) {\
                    return patternParts[1] + toNumbering(raw) + patternParts[3];\
                } else {\
                    return patternParts[1] + \
                        toNumbering(raw.substring(0, period)) +\
                        patternParts[2] +\
                        toNumbering(raw.substring(period + 1)) +\
                        patternParts[3];\
                }\
            }\
            \
            if (format.resolvedOptions().numberingSystem === numbering) {\
                // figure out prefixes, infixes, suffixes for positive and negative values\
                var posPatternParts = getPatternParts(true);\
                var negPatternParts = getPatternParts(false);\
                \
                Object.getOwnPropertyNames(testData).forEach(function (input) {\
                    var rawExpected = testData[input];\
                    var patternParts;\
                    if (rawExpected[0] === \"-\") {\
                        patternParts = negPatternParts;\
                        rawExpected = rawExpected.substring(1);\
                    } else {\
                        patternParts = posPatternParts;\
                    }\
                    var expected = buildExpected(rawExpected, patternParts);\
                    var actual = format.format(input);\
                    if (actual !== expected) {\
                        $ERROR(\"Formatted value for \" + input + \", \" +\
                        format.resolvedOptions().locale + \" and options \" +\
                        JSON.stringify(options) + \" is \" + actual + \"; expected \" + expected + \".\");\
                    }\
                });\
            }\
        });\
    });\
}\
\
\
/**\
 * Return the components of date-time formats.\
 * @return {Array} an array with all date-time components.\
 */\
\
function getDateTimeComponents() {\
    return [\"weekday\", \"era\", \"year\", \"month\", \"day\", \"hour\", \"minute\", \"second\", \"timeZoneName\"];\
}\
\
\
/**\
 * Return the valid values for the given date-time component, as specified\
 * by the table in section 12.1.1.\
 * @param {string} component a date-time component.\
 * @return {Array} an array with the valid values for the component.\
 */\
\
function getDateTimeComponentValues(component) {\
    \
    var components = {\
        weekday: [\"narrow\", \"short\", \"long\"],\
        era: [\"narrow\", \"short\", \"long\"],\
        year: [\"2-digit\", \"numeric\"],\
        month: [\"2-digit\", \"numeric\", \"narrow\", \"short\", \"long\"],\
        day: [\"2-digit\", \"numeric\"],\
        hour: [\"2-digit\", \"numeric\"],\
        minute: [\"2-digit\", \"numeric\"],\
        second: [\"2-digit\", \"numeric\"],\
        timeZoneName: [\"short\", \"long\"]\
    };\
    \
    var result = components[component];\
    if (result === undefined) {\
        $ERROR(\"Internal error: No values defined for date-time component \" + component + \".\");\
    }\
    return result;\
}\
\
\
/**\
 * Tests that the given value is valid for the given date-time component.\
 * @param {string} component a date-time component.\
 * @param {string} value the value to be tested.\
 * @return {boolean} true if the test succeeds.\
 * @exception if the test fails.\
 */\
\
function testValidDateTimeComponentValue(component, value) {\
    if (getDateTimeComponentValues(component).indexOf(value) === -1) {\
        $ERROR(\"Invalid value \" + value + \" for date-time component \" + component + \".\");\
    }\
    return true;\
}\
\
\
/**\
 * Verifies that the actual array matches the expected one in length, elements,\
 * and element order.\
 * @param {Array} expected the expected array.\
 * @param {Array} actual the actual array.\
 * @return {boolean} true if the test succeeds.\
 * @exception if the test fails.\
 */\
function testArraysAreSame(expected, actual) {\
    for (i = 0; i < Math.max(actual.length, expected.length); i++) {\
        if (actual[i] !== expected[i]) {\
            $ERROR(\"Result array element at index \" + i + \" should be \\\"\" +\
                expected[i] + \"\\\" but is \\\"\" + actual[i] + \"\\\".\");\
        }\
    }\
    return true;\
}\
\
";
