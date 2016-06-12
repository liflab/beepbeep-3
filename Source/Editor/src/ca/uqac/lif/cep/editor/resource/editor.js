//Yo
$(document).ready(function() {
	$(".processor-box").draggable();
	$("#new-proc").click(function() {
		$.ajax({
			"method" : "POST",
			"url" : "processor",
			"data" : {
				"type" : "ca.uqac.lif.cep.Passthrough"
			}
		}).done(function(data) {
			data.lines = [];
			boxes.push(data);
			create_div(data);
		});
	});
	$("#new-proc-and").click(function() {
		$.ajax({
			"method" : "POST",
			"url" : "processor",
			"data" : {
				"type" : "ca.uqac.lif.cep.ltl.And"
			}
		}).done(function(data) {
			data.lines = [];
			boxes.push(data);
			create_div(data);
		});
	});
	$("#connect").click(function() {
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
	});
});

var boxes = [];

var selected = [];

create_div = function(data)
{
	jQuery("<div/>", {
		id: "processor-box-" + data.id,
		"class": "processor-box",
		title: 'Some processor',
		width: data.width + "px",
		height: data.height + "px",
		css : {
			backgroundImage : "url('image?id=" + data.id + "')"
		}
	}).appendTo('#playground').draggable();
	for (var i = 0; i < data.inputs.length; i++)
	{
		jQuery("<div/>", {
			id: "processor-box-" + data.id + "-input-" + i,
			"class" : "processor-box-input",
			title: "Input " + i,
			css : {
				left: data.inputs[i].x + "px",
				top: data.inputs[i].y + "px"
			}
		}).appendTo("#processor-box-" + data.id).click(function() {
			selected.push($(this).attr("id"));
		});
	}
	for (var i = 0; i < data.outputs.length; i++)
	{
		jQuery("<div/>", {
			id: "processor-box-" + data.id + "-output-" + i,
			"class" : "processor-box-output",
			title: "Output " + i,
			css : {
				left: data.outputs[i].x + "px",
				top: data.outputs[i].y + "px"
			}
		}).appendTo("#processor-box-" + data.id).click(function() {
			selected.push($(this).attr("id"));
		});
	}
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

/* http://www.monkeyandcrow.com/blog/drawing_lines_with_css3/ */
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