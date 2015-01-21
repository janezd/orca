convert.graph <- function(graph) {
    if (is.matrix(graph))
        t(graph)
    else if (is.data.frame(graph))
        t(data.matrix(graph))
    else if (require("graph", quietly=TRUE)) {
        edges <- graph::edgeMatrix(graph)
        t(matrix(as.integer(edges), ncol(edges), nrow(edges)))
    }
    else stop("unrecognized graph type")
}

count4 <- function(graph) {
    edges <- convert.graph(graph) 
    .C("count4",
        edges, dim(edges),
        orbits=matrix(0, nrow=max(edges), ncol=15))$orbits
}

count5 <- function(graph) {
    edges <- convert.graph(graph) 
    .C("count5",
        edges, dim(edges),
        orbits=matrix(0, nrow=max(edges), ncol=73))$orbits
}

ecount4 <- function(graph) {
    edges <- convert.graph(graph) 
    .C("ecount4",
        edges, dim(edges),
        orbits=matrix(0, nrow=ncol(edges), ncol=12))$orbits
}

ecount5 <- function(graph) {
    edges <- convert.graph(graph) 
    .C("ecount5",
        edges, dim(edges),
        orbits=matrix(0, nrow=ncol(edges), ncol=68))$orbits
}
