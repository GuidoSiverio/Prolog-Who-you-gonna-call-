herramientasRequeridas(ordenarCuarto, [aspiradora(100), trapeador, plumero]).
herramientasRequeridas(limpiarTecho, [escoba, pala]).
herramientasRequeridas(cortarPasto, [bordedadora]).
herramientasRequeridas(limpiarBanio, [sopapa, trapeador]).
herramientasRequeridas(encerarPisos, [lustradpesora, cera, aspiradora(300)]).

persona(Persona):-
    tiene(Persona,_).

% Punto 1

tiene(egon, aspiradora(200)).
tiene(egon, trapeador).
tiene(peter, trapeador).
tiene(winston, varitaNeutrones).

% Punto 2

satisfaceNecesidad(Persona, Herramienta):-
    tiene(Persona, Herramienta).

satisfaceNecesidad(Persona, aspiradora(PotenciaRequerida)):-
    tiene(Persona, aspiradora(Potencia)),
    Potencia >= PotenciaRequerida.

% Punto 3
    
puedeRealizarTarea(Persona, Tarea):-
    herramientasRequeridas(Tarea, _),
    tiene(Persona, varitaNeutrones).

puedeRealizarTarea(Persona, Tarea):-
    persona(Persona),
    herramientasRequeridas(Tarea, Herramientas),
    forall(member(Elem, Herramientas), satisfaceNecesidad(Persona, Elem)).

% Punto 4

tareaPedida(Cliente, Tarea, M2).
precio(Tarea, PrecioPorM2).

dineroACobrar(Cliente, Precio):-
    findall(PrecioDeTarea, precioTotal(Cliente, PrecioDeTarea), Lista),
    sumlist(Lista, Precio).
    

precioTotal(Cliente, PrecioDeTarea):-
    tareaPedida(Cliente, Tarea, M2),
    precio(Tarea, PrecioPorM2),
    PrecioDeTarea is M2 * PrecioPorM2.   

% Punto 5

aceptariaPedido(ray, Cliente):-
    not(tareaPedida(Cliente, limpiarTecho, _)).

aceptariaPedido(winston, Cliente):-
    dineroACobrar(Cliente, Precio),
    Precio >= 500.

aceptariaPedido(peter, _).

aceptariaPedido(egon, Cliente):-
    forall(tareaPedida(Cliente, Tarea, _), not(tareaCompleja(Tarea))).

tareaCompleja(limpiarTecho).

tareaCompleja(Tarea):-
    herramientasRequeridas(Tarea, Herramientas), 
    length(Herramientas, Cantidad),
    Cantidad > 2.
    
% Punto 6

