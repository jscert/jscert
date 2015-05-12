
var tracer_items = [ 
{ type: 'enter_call', file: 'foo.ml', start_line: 4, start_col: 0, end_line: 5, end_col: 1 },
{ type: 'exit_call', file: 'foo.ml', start_line: 5, start_col: 1, end_line: 5, end_col: 1 },
{ type: 'enter_call', file: 'foo.ml', start_line: 5, start_col: 0, end_line: 5, end_col: 4 },
{ type: 'enter_call', file: 'bar.ml', start_line: 0, start_col: 4, end_line: 0, end_col: 1 },
{ type: 'exit_call', file: 'bar.ml', start_line: 0, start_col: 5, end_line: 0, end_col: 1 },
{ type: 'exit_call', file: 'foo.ml', start_line: 5, start_col: 1, end_line: 5, end_col: 4 },
];

var tracer_files = {
	'foo.ml':
	"fdsqfdsfsq\nfdsqfdf (* #sec-4.3.6 *) sfddsfsq\nfdsqfdsfdsfdsfsq\nfdsqfdfqdsfdsfsq\nfdfqdfqs\nfdsqfdsfdsfdsfsq\nfdsqfdfqdsfdsfsq\nfdfdsqfdsfdsfdsfsq\nfdsqfdfqdsfdsfsq\n",
	'bar.ml':
	"ffdffdfsffdsqfdsfds\n",
}
