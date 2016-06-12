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