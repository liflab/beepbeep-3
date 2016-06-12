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
		  var pb = new ProcessorBox(data.id);
		  boxes.push(pb);
		  pb.toDiv();
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
		  var pb = new ProcessorBox(data.id);
		  boxes.push(pb);
		  pb.toDiv();
	  });
  });
});

var boxes = [];

function ProcessorBox(id) 
{
	/**
	 * An array of coordinates, indicating the location of
	 * each of the processor's inputs within the box
	 */
	var m_inputPoints = [];
	
	/**
	 * An array of coordinates, indicating the location of
	 * each of the processor's outputs within the box
	 */
	var m_outputPoints = [];
	
	/**
	 * The height of the processor box, in pixels
	 */
	var m_height = 67;
	
	/**
	 * The width of the processor box, in pixels
	 */
	var m_width = 126;
	
	/**
	 * The processor ID this box corresponds to
	 */
	var m_id = id;
	
	/**
	 * Creates a DOM element representing that processor box
	 */
	this.toDiv = function()
	{
		jQuery('<div/>', {
		    id: 'processor-box-' + m_id,
		    title: 'Some processor',
		    width: m_width,
		    height: m_height,
		    css : {
		    	backgroundImage : "url('image?id=" + m_id + "')",
		    	display : "block",
		    	position: "absolute"
		    }
		}).appendTo('#playground');
		$("#processor-box-" + m_id).draggable();
	};
};

Coordinate = function()
{
	var x = 0;
	var y = 0;
};