// Yo
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
	jQuery('<div/>', {
	    id: 'processor-box-' + data.id,
	    title: 'Some processor',
	    width: data.width,
	    height: data.height,
	    css : {
	    	backgroundImage : "url('image?id=" + data.id + "')",
	    	display : "block",
	    	position: "absolute"
	    }
	}).appendTo('#playground').draggable();
};