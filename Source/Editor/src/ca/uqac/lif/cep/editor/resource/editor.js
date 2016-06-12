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
});

var boxes = [];

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
			id: "processor-box-input-" + i,
			"class" : "processor-box-input",
			title: "Input " + i,
			css : {
				left: data.inputs[i].x + "px",
				top: data.inputs[i].y + "px"
			}
		}).appendTo("#processor-box-" + data.id);
	}
	for (var i = 0; i < data.outputs.length; i++)
	{
		jQuery("<div/>", {
			id: "processor-box-output-" + i,
			"class" : "processor-box-output",
			title: "Output " + i,
			css : {
				left: data.outputs[i].x + "px",
				top: data.outputs[i].y + "px"
			}
		}).appendTo("#processor-box-" + data.id);
	}
};