# Contributions Welcome

We welcome contributions of any sort.
Whether you are a student, someone from industry, or an enthousiast, you are welcome to contribute.
As a student you can contribute while getting ECTS (as bachelor, master, [honors](http://honours.tudelft.nl/), or [language engineering](https://weblab.tudelft.nl/in4333/) project).
If you're from industry collaboration most likely means using the language and contributing features that you need yourself.
If you want to become a contributor feel free to contact us.

We have a wishlist for contributions, structured in the form of projects:

* New backends (for embedding in applications)
  * Python backend (in-memory)
  * C# backend (persisted data)
  * Google Go backend (in-memory or persisted)
  * peer2peer backend
  * JavaScript backend for calculating derived values on clients
  * WebSocket based backend for automatically updating values on clients
* New backends (full applications)
  * Create-Read-Update-Delete interface, but then better
  * Generic structured data editor for phones, communicating changes to other phones
* Infrastructure
  * Web-based language editor with a 'publish'-button that automatically publishes a webapplication
* Case studies
  * Use the Java backend to build a desktop application
  * Use the WebDSL backend to build a web application

Feel free to combine any of the above, such as building a backend for your favorite language, and using it in a case study.


## Python backend

Creating a Python backend would involve the following steps:

* A plan for what the backend should do, and what it should support in order to do this
* Designing what code to generate
* Defining a Python grammar in [SDF3](http://www.metaborg.org/sdf3/)
* Forking this project and implementing Python code generation in a `feature/Python-backend` branch
* Doing a pull-request

You will be working closely together with us, and will receive the necessary [Spoofax](http://www.metaborg.org/spoofax/) support to get you up and running.


## JavaScript backend for calculating derived values

The WebDSL backend computes all derived values on the server.
For applications it is often useful to calculate derived values based on values entered in forms before submitting the changes to the server.
To enable this, the values need to be calculated in JavaScript, on the client.

Creating a JavaScript backend would involved the following steps:

* Designing an architecture for the use client-side derived value calculation (where does data come from, how to update the DOM, etc.)
* Designing the code to generate
* Defining a JavaScript grammar in [SDF3](http://www.metaborg.org/sdf3/)
* Forking this project and implementing Python code generation in a `feature/JavaScript-backend` branch
* Doing a pull-request

You will be working closely together with us, and will receive the necessary [Spoofax](http://www.metaborg.org/spoofax/) support to get you up and running.


## Case Study
Do you have any project in which you need a data model, possible with derived value calculation?
How about using our language to define the model, and generate the Java (or some other language).
Generating the code for your model will save you time and let you focus on the rest of your application.
We would be very interested in your experience, and might even extend the language if you encounter situations which you cannot model.
