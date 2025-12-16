/*! \mainpage notitle
 * 
 * This is the API documentation for the
 * <a href="http://liflab.github.io/beepbeep-3">BeepBeep 3</a>
 * event stream processor.
 * 
 * \section whatis What is BeepBeep?
 
 * BeepBeep is a Java library for event stream processing and runtime analysis. It
 * provides a general-purpose framework for defining, composing, and executing
 * processors that transform one or more streams of events into derived streams,
 * possibly in real time.
 * 
 * At its core, BeepBeep models computation as a network of processors connected by
 * streams. Each processor consumes events from its input streams, applies a
 * well-defined operation, and produces output events incrementally, as data
 * becomes available. This architecture makes it possible to express a wide range
 * of tasks, from simple stream transformations to complex online queries and
 * runtime monitors.
 * 
 * BeepBeep emphasizes:
 * 
 *  - Compositionality: processors can be combined into larger processing
 *    graphs, enabling modular and reusable designs.
 *  - Determinism and precision: stream transformations are defined by explicit,
 *    well-scoped operators with clear semantics.
 *  - Flexibility: the library is domain-agnostic and can be used for log
 *    analysis, runtime verification, dataflow experimentation, or online
 *    analytics.
 *  - Extensibility: users can define custom processors and functions, or build
 *    higher-level abstractions on top of the core API.
 * 
 * Unlike many stream processing frameworks, BeepBeep is designed as a lightweight,
 * embeddable library rather than a distributed platform. It runs in-process,
 * requires no external services, and is suitable for integration into standalone
 * applications, experimental prototypes, or research tools.
 * 
 * The API documentation describes the core abstractions of the library, (such as
 * processors, functions, and connectors) as well as the standard processors
 * provided by BeepBeep and its optional extensions.
 * 
 * \section info More information
 *
 *  - Please first have a look at
 *    <a href="http://liflab.github.io/beepbeep-3">BeepBeep's website</a>.
 *    The documentation here only covers the API.
 *  - The library also comes with more than 150
 *    <a href="https://liflab.github.io/beepbeep-3-examples/">illustrated and
 *    documented code examples</a>, ranging from simple pipelines to concrete
 *    use cases.
 *  - For an in-depth tutorial on how to use BeepBeep, please refer to its
 *    <a href="https://liflab.gitbooks.io/event-stream-processing-with-beepbeep-3/">user
 *    manual</a>.
 *
 */
