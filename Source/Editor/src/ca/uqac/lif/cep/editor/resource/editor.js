/*
    BeepBeep, an event stream processor
    Copyright (C) 2008-2016 Sylvain Hallé

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU Lesser General Public License as published
    by the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU Lesser General Public License for more details.

    You should have received a copy of the GNU Lesser General Public License
    along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

/**
 * The set of processor boxes currently in use in the editor
 */
var boxes = [];

/**
 * The stack of elements that have been clicked since the last action
 */
var selected = [];

/**
 * Global variable to detect if an element is being dragged
 */
var is_dragging = false;

/**
 * Connects two processors
 */
function connect_processors()
{
	var parts_1 = selected.pop().split("-");
	var parts_2 = selected.pop().split("-");
	var id_out = -1;
	if (parts_1[3] === "output" && parts_2[3] === "input")
	{
		id_out = parts_1[2];
		var nb_out = parts_1[4];
		var id_in = parts_2[2];
		var nb_in = parts_2[4];
	}
	else if (parts_1[3] === "input" && parts_2[3] === "output")
	{
		id_out = parts_2[2];
		var nb_out = parts_2[4];
		var id_in = parts_1[2];
		var nb_in = parts_1[4];
	}
	if (id_out == -1)
	{
		return;
	}
	// Clear the stack
	selected = [];
	// Draw line
	draw_line(id_out, nb_out, id_in, nb_in);
	// Call the server
	$.ajax({
		"method" : "POST",
		"url" : "connect",
		"data" : {
			"input-id" : id_in,
			"input-nb" : nb_in,
			"output-id" : id_out,
			"output-nb" : nb_out
		}
	}).done(function(data) {
		console.log("Connected");
	});
};

/**
 * Creates a new palette, based on JSON data
 * @param data The data for the palette
 * @param id The palette ID
 */
function create_palette(data, id)
{
	var div = jQuery("<div/>", {
		"class": "processor-palette",
		"title": data.name
	});
	var ul = jQuery("<ul/>");
	for (var i = 0; i < data.entries.length; i++)
	{
		var entry = data.entries[i];
		var li = jQuery("<li/>", {
			"class": "palette-button",
			id: "palette-" + id + "-button-" + i,
			title: entry.processorname,
			css: {
				backgroundImage: "url('palette-button?id=" + id + "&nb=" + i + "')"
			}
		});
		//li.click(ajax_processor(entry.processorname));
		li.draggable({
	        revert : function(event, ui) {
	            // on older version of jQuery use "draggable"
	            // $(this).data("draggable")
	            // on 2.x versions of jQuery use "ui-draggable"
	            // $(this).data("ui-draggable")
	            $(this).data("uiDraggable").originalPosition = {
	                top : 0,
	                left : 0
	            };
	            // return boolean
	            return !event;
	            // that evaluate like this:
	            // return event !== false ? false : true;
	        },
	        revertDuration: 0,
	        stop : ajax_processor(entry.processorname)
	    });
		li.appendTo(ul);
	}
	ul.appendTo(div);
	div.draggable().resizable();
	return div;
};

/**
 * Closure to return
 * @param processorname
 * @returns {Function}
 */
function ajax_processor(processorname)
{
	return function(event)
	{
		console.log(event);
		$.ajax({
			"method" : "POST",
			"url" : "processor",
			"data" : {
				"type" : processorname,
				"x" : event.clientX - $("#playground").position().left,
				"y" : event.clientY - $("#playground").position().top,
			}
		}).done(function(data) {
			data.lines = [];
			boxes.push(data);
			create_div(data);
		});		
	};
};

/**
 * Create a new <tt>div</tt> element for a processor, based on the JSON
 * data provided by the editor. This function creates the main box for
 * the processor, and small boxes for each of the processor's inputs
 * and outputs. These boxes are placed at the coordinates specified in
 * the JSON.
 * 
 * @param data The JSON data
 */
function create_div(data)
{
	var box = jQuery("<div/>", {
		id: "processor-box-" + data.id,
		"class": "processor-box",
		title: data.name,
		width: data.width + "px",
		height: data.height + "px",
		css : {
			backgroundImage : "url('image?id=" + data.id + "')",
			left: data.x,
			top: data.y,
			marginLeft: -data.width / 2,
			marginTop: -data.height / 2
		}
	}).appendTo('#playground').draggable();
	box.mousedown(function() {
		is_dragging = false;
	}).mousemove(function() {
		is_dragging = true;
	}).mouseup(function() {
		var was_dragging = is_dragging;
	    is_dragging = false;
	    if (was_dragging) {
	    	dragged($(this));
	    }
	});
	for (var i = 0; i < data.inputs.length; i++)
	{
		create_input_box(data.id, i, data.inputs[i]);
	}
	for (var i = 0; i < data.outputs.length; i++)
	{
		create_output_box(data.id, i, data.outputs[i]);
	}
};

/**
 * Creates a <tt>div</tt> element for the input of a processor
 * @param id The ID of the box
 * @param i The number of the input
 * @param data The JSON data corresponding to that input
 */
function create_input_box(id, i, data)
{
	jQuery("<div/>", {
		id: "processor-box-" + id + "-input-" + i,
		"class" : "processor-box-input",
		title: "Input " + i,
		css : {
			left: data.x + "px",
			top: data.y + "px"
		}
	}).appendTo("#processor-box-" + id).click(function(e) {
		selected.push($(this).attr("id"));
	});
};

/**
 * Creates a <tt>div</tt> element for the output of a processor
 * @param id The ID of the box
 * @param i The number of the output
 * @param data The JSON data corresponding to that output
 */
function create_output_box(id, i, data)
{
	jQuery("<div/>", {
		id: "processor-box-" + id + "-output-" + i,
		"class" : "processor-box-output",
		title: "Output " + i,
		css : {
			left: data.x + "px",
			top: data.y + "px"
		}
	}).appendTo("#processor-box-" + id).click(function(e) {
		selected.push($(this).attr("id"));
	});
};

/**
 * Finds the box of given ID
 * @param box_id The ID of the box to find
 * @return The box
 */
function find_box(box_id)
{
	for (var i = 0; i < boxes.length; i++)
	{
		var box = boxes[i];
		if (box.id == box_id)
			return box;
	}
};

/**
 * Finds the div corresponding to the box of given ID
 * @param box_id The ID of the box to find
 * @return The div
 */
function find_div(box_id)
{
	return $("#processor-box-" + box_id);
};

/**
 * Draws a line
 */
function draw_line(out_id, out_nb, in_id, in_nb)
{
	var box_out = find_box(out_id);
	var box_in = find_box(in_id);
	var div_out_pos = find_div(out_id).position();
	var div_in_pos = find_div(in_id).position();
	var input = box_in.inputs[in_nb];
	var output = box_out.outputs[in_nb];
	var top_left_x = Math.min(div_in_pos.left + input.x, div_out_pos.left + output.x);
	var top_left_y = Math.min(div_in_pos.top + input.y, div_out_pos.top + output.y);
	var bot_right_x = Math.max(div_in_pos.left + input.x, div_out_pos.left + output.x);
	var bot_right_y = Math.max(div_in_pos.top + input.y, div_out_pos.top + output.y);
	var line = create_line(top_left_x, top_left_y, bot_right_x, bot_right_y);
	box_out.lines.push(line);
	box_in.lines.push(line);
	line.appendTo("#playground");
	/*var line_box = jQuery("<div/>", {
		"class": "pipe-box",
		height: bot_right_y - top_left_y,
		width: bot_right_x - top_left_x,
		css: {
			left: top_left_x,
			top: top_left_y
		}
	}).appendTo("#playground");
	if (output.o === "RIGHT" && input.o === "LEFT")
	{
		// Left-right line
		jQuery("<div/>", {
			"class": "line-box",
			css: {
				left: top_left_x,
				top: top_left_y
			}
		})

	}*/
};

/* From: http://www.monkeyandcrow.com/blog/drawing_lines_with_css3/
 * To be replaced with something more appropriate some day */
function create_line(x1,y1, x2,y2){
    var length = Math.sqrt((x1-x2)*(x1-x2) + (y1-y2)*(y1-y2));
  var angle  = Math.atan2(y2 - y1, x2 - x1) * 180 / Math.PI;
  var transform = 'rotate('+angle+'deg)';

    var line = $('<div>')
        .addClass('line')
        .css({
          'position': 'absolute',
          'transform': transform
        })
        .width(length)
        .offset({left: x1, top: y1});
    return line;
}

/**
 * Performs an update of the GUI when some element is clicked
 * @param element The element
 */
function clicked(element)
{
	
};

/**
 * Performs an update of the GUI when some element is dragged
 * @param element The element
 */
function dragged(element)
{
	var parts = element.attr("id").split("-");
	var id = parts[2];
	$.ajax({
		"method" : "POST",
		"url" : "move",
		"data" : {
			"id" : id,
			"x" : element.position().left,
			"y" : element.position().top
		}
	}).done(function(data) {
		// Do nothing
	});	
	console.log(element.attr("id"));
};

$(document).ready(function() {
	$.ajax({
		"method" : "GET",
		"url" : "palettes"
	}).done(function(data) {
		for (var i = 0; i < data.length; i++)
		{
			var pal = create_palette(data[i], i);
			pal.appendTo("#playground");
		}
	});
	$("#connect").click(connect_processors);
});